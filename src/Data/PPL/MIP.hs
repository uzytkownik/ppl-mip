{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
module Data.PPL.MIP
  (
    Var,
    LinearExpression,
    AffineExpression,
    AffineExpressionLike,
    Constraints,
    Objective(..),
    Integers(..),
    SolutionResult,
    MIPSolution,
    (%+),
    (%-),
    (%*),
    (%/),
    (%<=),
    (%==),
    (%>=),
    (%&&),
    var,
    sc,
    mipSolve,

    name,
    constant,
    _Unfeasable,
    _Unbounded,
    _Optimized,
    _Maximize,
    _Minimize
  )
where
import           Control.Lens
import           Control.Monad.State.Strict
import qualified Data.Foldable       as F
import           Data.Map(Map)
import qualified Data.Map            as M
import           Data.Ratio
import           Data.Typeable
import           Foreign.PPL
import           System.IO.Unsafe

newtype Var = Var {_name :: String} deriving (Eq, Ord, Typeable)

makeLenses ''Var

var :: String -> Var
var = Var

sc :: Rational -> Rational
sc = id

newtype LinearExpression = LinearExpression {_coeff_ :: Map Var Rational} deriving (Eq, Ord, Typeable)
data AffineExpression = AffineExpression {_linear_ :: LinearExpression, _constant :: Rational} deriving (Eq, Ord, Typeable)

makeClassy ''LinearExpression
makeLenses ''AffineExpression

instance HasLinearExpression AffineExpression where
    linearExpression = linear_

type instance Index LinearExpression = Var
type instance IxValue LinearExpression = Rational
instance Ixed LinearExpression where
    ix v = coeff_ . at v . lens (maybe 0 id) (const conv)
           where conv 0 = Nothing
                 conv x = Just $! x

class AffineExpressionLike l where
  toAffineExpression :: l -> AffineExpression

instance AffineExpressionLike AffineExpression where
  toAffineExpression = id

instance AffineExpressionLike LinearExpression where
  toAffineExpression le = AffineExpression le 0

instance AffineExpressionLike Rational where
  toAffineExpression s = AffineExpression (LinearExpression M.empty) s

instance AffineExpressionLike Var where
  toAffineExpression v = AffineExpression (LinearExpression (M.singleton v 1)) 0

class AffineExpressionLike b => ScalarMultiple a b | a -> b where
  (%*) :: Rational -> a -> b
  (%/) :: a -> Rational -> b
  e %/ v = (1 / v) %* e

infixl 7 %*, %/

instance ScalarMultiple Var LinearExpression where
  a %* v = LinearExpression (M.singleton v a)

instance ScalarMultiple LinearExpression LinearExpression where
  (%*) a = coeff_ . traversed %~ (* a)

instance ScalarMultiple AffineExpression AffineExpression where
  (%*) a = (coeff_ . traversed %~ (* a)) . (constant %~ (* a))

class Additive a b c | a b -> c where
  (%+) :: a -> b -> c
  (%-) :: a -> b -> c

infixl 6 %+, %-

instance Additive Var Var LinearExpression where
   v %+ v' = LinearExpression $! M.unionWith (+) (M.singleton v 1) (M.singleton v' 1)
   v %- v' = LinearExpression $! M.unionWith (+) (M.singleton v 1) (M.singleton v' (-1))

instance Additive LinearExpression LinearExpression LinearExpression where
  (LinearExpression le) %+ (LinearExpression le') = LinearExpression $! M.unionWith (+) le le'
  (LinearExpression le) %- (LinearExpression le') = LinearExpression $! M.unionWith (+) le (M.map negate le')

instance Additive LinearExpression Var LinearExpression where
  (LinearExpression le) %+ v = LinearExpression $! M.unionWith (+) le (M.singleton v 1)
  (LinearExpression le) %- v = LinearExpression $! M.unionWith (+) le (M.singleton v (-1))

instance Additive Var LinearExpression LinearExpression where
  v %+ (LinearExpression le) = LinearExpression $! M.unionWith (+) (M.singleton v 1) le
  v %- le = v %+ (-1) %* le

instance Additive LinearExpression Rational AffineExpression where
  le %+ r = AffineExpression le r
  le %- r = AffineExpression le (negate r)

instance Additive Rational LinearExpression AffineExpression where
  r %+ le = AffineExpression le r
  r %- le = AffineExpression ((-1) %* le) r

instance Additive AffineExpression AffineExpression AffineExpression where
  (AffineExpression le s) %+ (AffineExpression le' s') = AffineExpression (le %+ le') (s + s')
  (AffineExpression le s) %- (AffineExpression le' s') = AffineExpression (le %- le') (s - s')

instance Additive AffineExpression Var AffineExpression where
  (AffineExpression le s) %+ v = AffineExpression (le %+ v) s
  (AffineExpression le s) %- v = AffineExpression (le %- v) s

instance Additive Var AffineExpression AffineExpression where
  v %+ (AffineExpression le s) = AffineExpression (v %+ le) s
  v %- (AffineExpression le s) = AffineExpression (v %- le) (negate s)

instance Additive AffineExpression Rational AffineExpression where
  (AffineExpression le s) %+ r = AffineExpression le (s + r)
  (AffineExpression le s) %- r = AffineExpression le (s - r)

instance Additive Rational AffineExpression AffineExpression where
  r %+ (AffineExpression le s) = AffineExpression le (r + s)
  r %- (AffineExpression le s) = AffineExpression ((-1) %* le) (r - s)

data Constraints = Constraints [(AffineExpression, ConstraintType)] deriving (Eq,Typeable)

(%<=) :: (AffineExpressionLike l, AffineExpressionLike l') =>
         l -> l' -> Constraints
l %<= l' = Constraints [(toAffineExpression l' %- toAffineExpression l, GreaterOrEqual)]

(%==) :: (AffineExpressionLike l, AffineExpressionLike l') =>
         l -> l' -> Constraints
l %== l' = Constraints [(toAffineExpression l %- toAffineExpression l', Equal)]

(%>=) :: (AffineExpressionLike l, AffineExpressionLike l') =>
         l -> l' -> Constraints
l %>= l' = Constraints [(toAffineExpression l %- toAffineExpression l', GreaterOrEqual)]

infix 4 %<=, %==, %>=

(%&&) :: Constraints -> Constraints -> Constraints
Constraints s %&& Constraints s' = Constraints (s ++ s')

infixr 3 %&&

newtype Integers = Integers [Var] deriving (Eq,Typeable)

newtype MIPSolution s = MIPSolution {_solution_ :: Map String s} deriving (Eq,Show)
makeLenses ''MIPSolution

instance Functor MIPSolution where
  f `fmap` (MIPSolution v) = MIPSolution (M.map f v)

type instance Index (MIPSolution s) = Var
type instance IxValue (MIPSolution s) = s
instance Ixed (MIPSolution s) where
    ix (Var v) = solution_ . ix v

type NumberState = (Map String PPLDimentionType, PPLDimentionType)

leToILE :: AffineExpression -> (Integer, Map Var Integer)
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
  let go v s' = (\n -> (n, s')) <$> numberVar v
      (s, l) = leToILE le
  in (\m -> (-s, F.toList m)) <$> M.traverseWithKey go l

numberCs :: Constraints -> State NumberState [(Integer, [(PPLDimentionType, Integer)], ConstraintType)]
numberCs (Constraints cs) =
  forM cs $ \(le, ct) -> (\(s, lc) -> (s, lc, ct)) <$> numberAe le

mipSolve :: AffineExpressionLike l => Constraints -> Objective l -> Integers -> SolutionResult (MIPSolution Rational)
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

