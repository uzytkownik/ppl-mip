{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
module Data.PPL.MIP
  (
    Var,
    LinearExpression,
    AffineExpression,
    HasLinearExpression,
    AffineExpressionLike,
    Constraints,
    Objective(..),
    Integers(..),
    SolutionResult,
    MIPSolution,
    (%*),
    (%/),
    (%+),
    (%-),
    (%<),
    (%<=),
    (%==),
    (%>=),
    (%>),
    (%&&),
    var,
    sc,
    lpSolve,
    mipSolve,
    subst,
    -- * Lens helpers
    name,
    constant,
    lvar,
    _Unfeasable,
    _Unbounded,
    _Optimized,
    _Maximize,
    _Minimize
  )
where
import           Control.Arrow
import           Control.Lens
import           Control.Monad.State.Strict
import           Data.String
import qualified Data.Foldable       as F
import           Data.Map(Map)
import qualified Data.Map            as M
import           Data.Ratio
import           Data.Typeable
import           Foreign.PPL
import           System.IO.Unsafe

-- | A free variable in equation.
newtype Var = Var {_name :: String} deriving (Eq, Typeable)

instance Show Var where
  show (Var v) = v

makeLenses ''Var

-- | Make variable out of `String`.
var :: String -> Var
var = Var

-- | Create a scalar. This is equivalend to `id` specialized to `Rational`.
sc :: Rational -> Rational
sc = id

instance IsString Var where
  fromString = Var

-- | Linear expression (function). This is a linear combination of `Var`s
-- without a scalar component.
newtype LinearExpression = LinearExpression {_coeff_ :: Map String Rational} deriving (Eq, Typeable)
-- | Affine expression. This is a sum of linear component and a scalar.
data AffineExpression = AffineExpression {_linear_ :: LinearExpression, _constant :: Rational} deriving (Eq, Typeable)

makeClassy ''LinearExpression
makeLenses ''AffineExpression

instance HasLinearExpression AffineExpression where
  linearExpression = linear_

type instance Index LinearExpression = Var
type instance IxValue LinearExpression = Rational
instance Ixed LinearExpression where
    ix = lvar

lvar :: HasLinearExpression l => Var -> Lens' l Rational
lvar (Var v) = coeff_ . at v . lens (maybe 0 id) (const conv)
               where conv 0 = Nothing
                     conv x = Just $! x


genStr :: HasLinearExpression l => Maybe String -> l -> Maybe String
genStr = ifoldrOf (coeff_ . itraversed) f
         where f v c = let r = case (numerator c, denominator c) of
                                 (1, 1) -> v
                                 (x, 1) -> show x ++ " " ++ v
                                 (x, y) -> show x ++ "/" ++ show y ++ show " " ++ v
                       in maybe (Just r) (Just . ((r ++ " + ") ++))

instance Show LinearExpression where
  show = maybe "" id . genStr Nothing

instance Show AffineExpression where
  show a = maybe "" id . genStr c $ a
           where c = case a ^. constant . to (numerator &&& denominator) of
                       (0, _) -> Nothing
                       (x, 1) -> Just $! show x
                       (x, y) -> Just $! show x ++ "/" ++ show y

-- | Anything that can be converted to an affine expression
class AffineExpressionLike l where
  toAffineExpression :: l -> AffineExpression

instance AffineExpressionLike AffineExpression where
  toAffineExpression = id

instance AffineExpressionLike LinearExpression where
  toAffineExpression le = AffineExpression le 0

instance AffineExpressionLike Rational where
  toAffineExpression s = AffineExpression (LinearExpression M.empty) s

instance AffineExpressionLike Var where
  toAffineExpression (Var v) = AffineExpression (LinearExpression (M.singleton v 1)) 0

class ScalarMultiple a b | a -> b where
  -- | Multiply by a rational number
  (%*) :: Rational -> a -> b
  -- | Divide by a rational number
  (%/) :: a -> Rational -> b
  e %/ v = (1 / v) %* e

infixl 7 %*, %/

instance ScalarMultiple Var LinearExpression where
  a %* Var v = LinearExpression (M.singleton v a)

instance ScalarMultiple LinearExpression LinearExpression where
  (%*) a = coeff_ . traversed %~ (* a)

instance ScalarMultiple AffineExpression AffineExpression where
  (%*) a = (coeff_ . traversed %~ (* a)) . (constant %~ (* a))

class Add a b c | a b -> c where
  -- | Add two expressions
  (%+) :: a -> b -> c
  -- | Divide two expressions
  (%-) :: a -> b -> c

infixl 6 %+, %-

instance Add Var Var LinearExpression where
   Var v %+ Var v' = LinearExpression $! M.unionWith (+) (M.singleton v 1) (M.singleton v' 1)
   Var v %- Var v' = LinearExpression $! M.unionWith (+) (M.singleton v 1) (M.singleton v' (-1))

instance Add LinearExpression LinearExpression LinearExpression where
  (LinearExpression le) %+ (LinearExpression le') = LinearExpression $! M.unionWith (+) le le'
  (LinearExpression le) %- (LinearExpression le') = LinearExpression $! M.unionWith (+) le (M.map negate le')

instance Add LinearExpression Var LinearExpression where
  (LinearExpression le) %+ Var v = LinearExpression $! M.unionWith (+) le (M.singleton v 1)
  (LinearExpression le) %- Var v = LinearExpression $! M.unionWith (+) le (M.singleton v (-1))

instance Add Var LinearExpression LinearExpression where
  Var v %+ (LinearExpression le) = LinearExpression $! M.unionWith (+) (M.singleton v 1) le
  Var v %- le = Var v %+ (-1) %* le

instance Add LinearExpression Rational AffineExpression where
  le %+ r = AffineExpression le r
  le %- r = AffineExpression le (negate r)

instance Add Rational LinearExpression AffineExpression where
  r %+ le = AffineExpression le r
  r %- le = AffineExpression ((-1) %* le) r

instance Add AffineExpression AffineExpression AffineExpression where
  (AffineExpression le s) %+ (AffineExpression le' s') = AffineExpression (le %+ le') (s + s')
  (AffineExpression le s) %- (AffineExpression le' s') = AffineExpression (le %- le') (s - s')

instance Add AffineExpression Var AffineExpression where
  (AffineExpression le s) %+ v = AffineExpression (le %+ v) s
  (AffineExpression le s) %- v = AffineExpression (le %- v) s

instance Add Var AffineExpression AffineExpression where
  v %+ (AffineExpression le s) = AffineExpression (v %+ le) s
  v %- (AffineExpression le s) = AffineExpression (v %- le) (negate s)

instance Add AffineExpression Rational AffineExpression where
  (AffineExpression le s) %+ r = AffineExpression le (s + r)
  (AffineExpression le s) %- r = AffineExpression le (s - r)

instance Add Rational AffineExpression AffineExpression where
  r %+ (AffineExpression le s) = AffineExpression le (r + s)
  r %- (AffineExpression le s) = AffineExpression ((-1) %* le) (r - s)

subst :: (HasLinearExpression l, ScalarMultiple s i, Add i l r) => Var -> s -> l -> r
subst v s = uncurry (%+) . first (%* s) . (lvar v <<.~ 0)

data Constraints = Constraints [(AffineExpression, ConstraintType)] deriving (Eq,Typeable)

-- | Declares that first argument is lower to second one.
(%<) :: (AffineExpressionLike l, AffineExpressionLike l') =>
        l -> l' -> Constraints
l %< l' = Constraints [(toAffineExpression l' %- toAffineExpression l, GreaterThan)]

-- | Declares that first argument is lower or equal to second one.
(%<=) :: (AffineExpressionLike l, AffineExpressionLike l') =>
         l -> l' -> Constraints
l %<= l' = Constraints [(toAffineExpression l' %- toAffineExpression l, GreaterOrEqual)]

-- | Declares that both arguments are equal.
(%==) :: (AffineExpressionLike l, AffineExpressionLike l') =>
         l -> l' -> Constraints
l %== l' = Constraints [(toAffineExpression l %- toAffineExpression l', Equal)]

-- | Declares that first argument is greated or equal to second one.
(%>=) :: (AffineExpressionLike l, AffineExpressionLike l') =>
         l -> l' -> Constraints
l %>= l' = Constraints [(toAffineExpression l %- toAffineExpression l', GreaterOrEqual)]

-- | Declares that first argument is greated or equal to second one.
(%>) :: (AffineExpressionLike l, AffineExpressionLike l') =>
        l -> l' -> Constraints
l %> l' = Constraints [(toAffineExpression l %- toAffineExpression l', GreaterThan)]

infix 4 %<, %<=, %==, %>=, %>

-- | Combines two constraints together
(%&&) :: Constraints -> Constraints -> Constraints
Constraints s %&& Constraints s' = Constraints (s ++ s')

infixr 3 %&&

-- | List of variables that are an integer
newtype Integers = Integers [Var] deriving (Eq,Typeable)

-- | A solution to a MIP problem.
newtype MIPSolution s = MIPSolution {_solution_ :: Map String s} deriving (Eq,Show)
makeLenses ''MIPSolution

instance Functor MIPSolution where
  f `fmap` (MIPSolution v) = MIPSolution (M.map f v)

type instance Index (MIPSolution s) = Var
type instance IxValue (MIPSolution s) = s
instance Ixed (MIPSolution s) where
    ix (Var v) = solution_ . ix v

type NumberState = (Map String PPLDimentionType, PPLDimentionType)

leToILE :: AffineExpression -> (Integer, Map String Integer)
leToILE (AffineExpression (LinearExpression m) s) =
  let d = F.foldr (gcd . denominator) (denominator s) m
      norm v = numerator v * (d `div` denominator v)
  in (norm s, norm <$> m)

numberVar :: Var -> State NumberState PPLDimentionType
numberVar (Var v) =
  state $ \s@(m, n) -> case M.lookup v m of
    Just v' -> (v', s)
    Nothing -> (n, (M.insert v n m, n + 1))

numberAe :: AffineExpression -> State NumberState (Integer, [(PPLDimentionType, Integer)])
numberAe le =
  let go v s' = (\n -> (n, s')) <$> numberVar (Var v)
      (s, l) = leToILE le
  in (\m -> (-s, F.toList m)) <$> M.traverseWithKey go l

numberCs :: Constraints -> State NumberState [(Integer, [(PPLDimentionType, Integer)], ConstraintType)]
numberCs (Constraints cs) =
  forM cs $ \(le, ct) -> (\(s, lc) -> (s, lc, ct)) <$> numberAe le

-- | Solve a linear problem.
lpSolve :: (AffineExpressionLike l) => Constraints -> Objective l -> SolutionResult (MIPSolution Rational)
lpSolve cs obj = mipSolve cs obj $! Integers []

-- | Solve a mixed integer problem.
mipSolve :: (AffineExpressionLike l) => Constraints -> Objective l -> Integers -> SolutionResult (MIPSolution Rational)
mipSolve cs obj (Integers int) = unsafePerformIO $! do
  pplInitialize
  (renumber <$>) <$> (withMipProblem dim cs' obj' int' $ solve dim)
  where ((cs', obj', int'), (varMap, dim)) =
          flip runState (M.empty, 0) $ (,,) <$> numberCs cs
                                            <*> traverse (numberAe . toAffineExpression) obj
                                            <*> mapM numberVar int
        renumber v = MIPSolution $! M.map f varMap
                     where f n = v !! fromIntegral n

-- Lens helpers
makePrisms ''Objective
makePrisms ''SolutionResult
