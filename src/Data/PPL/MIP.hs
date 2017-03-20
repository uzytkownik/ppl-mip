{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
module Data.PPL.MIP
  (
    Var,
    Scalar(..),
    LinearExpression,
    AffineExpression,
    HasLinearExpression,
    AffineExpressionLike(..),
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
    -- * Substitutions
    Subst(..),
    SubstConfLE(..),
    SubstConfAE(..),
    SubstConfLE'(..),
    SubstConfAE'(..),
    HasSubstConfLE(..),
    -- * Lens helpers
    name,
    scalar,
    constant,
    lvar,
    coeff,
    exprs,
    constr,
    _Unfeasable,
    _Unbounded,
    _Optimized,
    _Maximize,
    _Minimize,
    addScalar
  )
where
import           Control.Arrow
import           Control.Lens
import           Control.Monad.Fix
import           Control.Monad.State.Strict
import           Control.Monad.Writer.Strict
import           Data.Semigroup
import           Data.String
import           Data.Map(Map)
import qualified Data.Map            as M
import           Data.Ratio
import           Data.Typeable
import           Foreign.PPL
import           System.IO.Unsafe

-- | A free variable in equation.
newtype Var = Var {_name :: String} deriving (Eq, Typeable)
newtype Scalar a = Scalar {_scValue :: a} deriving (Eq, Typeable)

instance Show Var where
  show (Var v) = v
instance Show a => Show (Scalar a) where
  show (Scalar s) = show s

makeLenses ''Var

scalar :: Iso (Scalar a) (Scalar b) a b
scalar = iso _scValue Scalar

-- | Make variable out of `String`.
var :: String -> Var
var = Var

-- | Create a scalar.
sc :: Rational -> Scalar Rational
sc = Scalar

instance IsString Var where
  fromString = Var

instance Num a => Num (Scalar a) where
  (+) = scCombine (+)
  (-) = scCombine (-)
  (*) = scCombine (*)
  negate = Scalar . (view $ scalar . to negate)
  abs = Scalar . (view $ scalar . to abs)
  signum = Scalar . (view $ scalar . to signum)
  fromInteger = Scalar . (view $ to fromInteger)

instance Fractional a => Fractional (Scalar a) where
  (/) = scCombine (/)
  recip = Scalar . (view $ scalar . to recip)
  fromRational = Scalar . (view $ to fromRational)

instance Ord a => Ord (Scalar a) where
  compare (Scalar a) (Scalar b) = compare a b
  Scalar a < Scalar b = a < b
  Scalar a <= Scalar b = a <= b
  Scalar a > Scalar b = a > b
  Scalar a >= Scalar b = a >= b
  max = scCombine max
  min = scCombine min

instance Real a => Real (Scalar a) where
  toRational (Scalar s) = toRational s

scCombine :: (a -> a -> a) -> Scalar a -> Scalar a -> Scalar a
scCombine f = curry $ Scalar . (view $ alongside scalar scalar . to (uncurry f))

-- | Linear expression (function). This is a linear combination of `Var`s
-- without a scalar component.
newtype LinearExpression s = LinearExpression {_coeff_ :: Map String s} deriving (Eq, Typeable)
-- | Affine expression. This is a sum of linear component and a scalar.
data AffineExpression s = AffineExpression {_linear_ :: LinearExpression s, _constant :: s} deriving (Eq, Typeable)

makeClassy ''LinearExpression
makeLenses ''AffineExpression

instance HasLinearExpression (AffineExpression s) s where
    linearExpression = linear_

class HasScalars l where
    scalars :: Traversal (l s) (l s') s s'

instance HasScalars LinearExpression where
    scalars = iso _coeff_ LinearExpression . traversed

instance HasScalars AffineExpression where
    scalars = iso (_linear_ &&& _constant) (uncurry AffineExpression) . beside scalars id

instance Functor LinearExpression where
    fmap = (scalars %~)

instance Functor AffineExpression where
    fmap = (scalars %~)

type instance Index (LinearExpression s) = Var
type instance IxValue (LinearExpression s) = s
instance (Num s, Eq s) => Ixed (LinearExpression s) where
    ix = lvar

lvar :: (HasLinearExpression l s, Num s, Eq s) => Var -> Lens' l s
lvar (Var v) = coeff_ . at v . lens (maybe 0 id) (const conv)
               where conv 0 = Nothing
                     conv x = Just $! x

coeff :: HasLinearExpression l s => IndexedTraversal' Var l s
coeff f = coeff_ . iso M.toList M.fromList $ traverse (\(x, a) -> (,) x <$> indexed f (Var x) a)

genStr :: HasLinearExpression l Rational => Maybe String -> l -> Maybe String
genStr = ifoldrOf (coeff_ . itraversed) f
         where f v c = let r = case (numerator c, denominator c) of
                                 (1, 1) -> v
                                 (x, 1) -> show x ++ " " ++ v
                                 (x, y) -> show x ++ "/" ++ show y ++ show " " ++ v
                       in maybe (Just r) (Just . ((r ++ " + ") ++))

instance Show (LinearExpression Rational) where
  show = maybe "" id . genStr Nothing

instance Show (AffineExpression Rational) where
  show a = maybe "" id . genStr c $ a
           where c = case a ^. constant . to (numerator &&& denominator) of
                       (0, _) -> Nothing
                       (x, 1) -> Just $! show x
                       (x, y) -> Just $! show x ++ "/" ++ show y

instance Num s => Semigroup (LinearExpression s)
instance Num s => Monoid (LinearExpression s) where
  mempty = LinearExpression M.empty
  mappend = (%+)

instance Num s => Semigroup (AffineExpression s)
instance Num s => Monoid (AffineExpression s) where
  mempty = AffineExpression mempty 0
  mappend = (%+)

-- | Anything that can be converted to an affine expression
class AffineExpressionLike l s where
  toAffineExpression :: l -> AffineExpression s

instance AffineExpressionLike (AffineExpression s) s where
  toAffineExpression = id

instance Num s => AffineExpressionLike (LinearExpression s) s where
  toAffineExpression le = AffineExpression le 0

instance AffineExpressionLike (Scalar s) s where
  toAffineExpression (Scalar s) = AffineExpression (LinearExpression M.empty) s

instance Num s => AffineExpressionLike Var s where
  toAffineExpression (Var v) = AffineExpression (LinearExpression (M.singleton v 1)) 0

class ScalarMultiple s a b | s a -> b where
  -- | Multiply by a rational number
  (%*) :: Scalar s -> a -> b

-- | Divide by a rational number
(%/) :: (Fractional s, ScalarMultiple s a b) => a -> Scalar s -> b
e %/ Scalar v = Scalar (recip v) %* e

infixl 7 %*, %/

instance Num s => ScalarMultiple s (Scalar s) (Scalar s) where
  Scalar a %* Scalar b = Scalar $ a * b

instance ScalarMultiple s Var (LinearExpression s) where
  Scalar a %* Var v = LinearExpression (M.singleton v a)

instance Num s => ScalarMultiple s (LinearExpression s) (LinearExpression s) where
  (%*) (Scalar a) = coeff_ . traversed %~ (* a)

instance Num s => ScalarMultiple s (AffineExpression s) (AffineExpression s) where
  (%*) (Scalar a) = (coeff_ . traversed %~ (* a)) . (constant %~ (* a))

class Add a b c | a b -> c where
  -- | Add two expressions
  (%+) :: a -> b -> c
  -- | Divide two expressions
  (%-) :: a -> b -> c

infixl 6 %+, %-

instance Num s => Add (Scalar s) (Scalar s) (Scalar s) where
   v %+ v' = v + v'
   v %- v' = v - v'

instance Add Var Var (LinearExpression Rational) where
   Var v %+ Var v' = LinearExpression $! M.unionWith (+) (M.singleton v 1) (M.singleton v' 1)
   Var v %- Var v' = LinearExpression $! M.unionWith (+) (M.singleton v 1) (M.singleton v' (-1))

instance Num s => Add (LinearExpression s) (LinearExpression s) (LinearExpression s) where
  (LinearExpression le) %+ (LinearExpression le') = LinearExpression $! M.unionWith (+) le le'
  (LinearExpression le) %- (LinearExpression le') = LinearExpression $! M.unionWith (+) le (M.map negate le')

instance Num s => Add (LinearExpression s) Var (LinearExpression s) where
  (LinearExpression le) %+ Var v = LinearExpression $! M.unionWith (+) le (M.singleton v 1)
  (LinearExpression le) %- Var v = LinearExpression $! M.unionWith (+) le (M.singleton v (-1))

instance Num s => Add Var (LinearExpression s) (LinearExpression s) where
  Var v %+ (LinearExpression le) = LinearExpression $! M.unionWith (+) (M.singleton v 1) le
  Var v %- le = Var v %+ Scalar (-1 :: s) %* le

instance Num s => Add (LinearExpression s) (Scalar s) (AffineExpression s) where
  le %+ (Scalar r) = AffineExpression le r
  le %- (Scalar r) = AffineExpression le (negate r)

instance Num s => Add (Scalar s) (LinearExpression s) (AffineExpression s) where
  (Scalar r) %+ le = AffineExpression le r
  (Scalar r) %- le = AffineExpression (Scalar (-1 :: s) %* le) r

instance Num s => Add (AffineExpression s) (AffineExpression s) (AffineExpression s) where
  (AffineExpression le s) %+ (AffineExpression le' s') = AffineExpression (le %+ le') (s + s')
  (AffineExpression le s) %- (AffineExpression le' s') = AffineExpression (le %- le') (s - s')

instance Num s => Add (AffineExpression s) (LinearExpression s) (AffineExpression s) where
  (AffineExpression le s) %+ le' = AffineExpression (le %+ le') s
  (AffineExpression le s) %- le' = AffineExpression (le %- le') s

instance Num s => Add (LinearExpression s) (AffineExpression s) (AffineExpression s) where
  le %+ (AffineExpression le' s) = AffineExpression (le %+ le') s
  le %- (AffineExpression le' s) = AffineExpression (le %- le') (negate s)

instance Num s => Add (AffineExpression s) Var (AffineExpression s) where
  (AffineExpression le s) %+ v = AffineExpression (le %+ v) s
  (AffineExpression le s) %- v = AffineExpression (le %- v) s

instance Num s => Add Var (AffineExpression s) (AffineExpression s) where
  v %+ (AffineExpression le s) = AffineExpression (v %+ le) s
  v %- (AffineExpression le s) = AffineExpression (v %- le) (negate s)

instance Num s => Add (AffineExpression s) (Scalar s) (AffineExpression s) where
  (AffineExpression le s) %+ (Scalar r) = AffineExpression le (s + r)
  (AffineExpression le s) %- (Scalar r) = AffineExpression le (s - r)

instance Num s => Add (Scalar s) (AffineExpression s) (AffineExpression s) where
  (Scalar r) %+ (AffineExpression le s) = AffineExpression le (r + s)
  (Scalar r) %- (AffineExpression le s) = AffineExpression (Scalar (-1 :: s) %* le) (r - s)

newtype Constraints s = Constraints {_constr :: [(AffineExpression s, ConstraintType, AffineExpression s)]} deriving (Eq,Typeable)

makeLenses ''Constraints

-- | Declares that first argument is lower to second one.
(%<) :: (AffineExpressionLike l s, AffineExpressionLike l' s) =>
        l -> l' -> Constraints s
l %< l' = Constraints [(toAffineExpression l, LessThan, toAffineExpression l')]

-- | Declares that first argument is lower or equal to second one.
(%<=) :: (AffineExpressionLike l s, AffineExpressionLike l' s) =>
         l -> l' -> Constraints s
l %<= l' = Constraints [(toAffineExpression l, LessOrEqual, toAffineExpression l')]

-- | Declares that both arguments are equal.
(%==) :: (AffineExpressionLike l s, AffineExpressionLike l' s) =>
         l -> l' -> Constraints s
l %== l' = Constraints [(toAffineExpression l, Equal, toAffineExpression l')]

-- | Declares that first argument is greated or equal to second one.
(%>=) :: (AffineExpressionLike l s, AffineExpressionLike l' s) =>
         l -> l' -> Constraints s
l %>= l' = Constraints [(toAffineExpression l, GreaterOrEqual, toAffineExpression l')]

-- | Declares that first argument is greated or equal to second one.
(%>) :: (AffineExpressionLike l s, AffineExpressionLike l' s) =>
        l -> l' -> Constraints s
l %> l' = Constraints [(toAffineExpression l, GreaterThan, toAffineExpression l')]

infix 4 %<, %<=, %==, %>=, %>

-- | Combines two constraints together
(%&&) :: Constraints s -> Constraints s -> Constraints s
Constraints s %&& Constraints s' = Constraints (s ++ s')

infixr 3 %&&

instance Semigroup (Constraints s)
instance Monoid (Constraints s) where
  mempty = Constraints []
  mappend = (%&&)

exprs :: Traversal' (Constraints s) (AffineExpression s)
exprs = constr . each . roll . alongside id _2 . both
        where roll = iso (\(x, y, z) -> (x, (y, z))) (\(x, (y, z)) -> (x, y, z))

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

first' :: Monad m => (a -> m b) -> (a, c) -> m (b, c)
first' f (a, c) = flip (,) c <$> f a

mapMOf' :: (Monad m, Monoid r) => Getting (Sequenced () (WriterT r m)) s a -> (a -> m r) -> s -> m r
mapMOf' l f = fmap snd . runWriterT . mapMOf_ l (tell <=< lift . f)

with :: a -> Lens s t (s, a) (t, b)
with x = lens ((,) ?? x) (const $ fst)

zoom' :: MonadState s m => Lens' s s' -> State s' a -> m a
zoom' l s = state (runState (zoom l s))

mfix' :: MonadFix m => (b -> m (a, b)) -> m a
mfix' f = fmap fst $ mfix (f . snd)

newtype MonoidInApp m r = MonoidInApp {getMonoidInApp :: m r}

instance (Monoid r, Applicative m) => Monoid (MonoidInApp m r) where
    mempty = MonoidInApp $ pure mempty
    mappend (MonoidInApp l) (MonoidInApp r) = MonoidInApp (mappend <$> l <*> r)

useMap :: MonadState s m => Getting (MonoidInApp m a) s b -> (b -> m a) -> m a
useMap l f = join . fmap getMonoidInApp . use $ l . to f . iso MonoidInApp getMonoidInApp

newtype LCM a = LCM a

instance Integral a => Semigroup (LCM a) where
    LCM a <> LCM b = LCM $ gcd a b
    stimes _ x = x

numberVar :: Monad m => Var -> StateT NumberState m PPLDimentionType
numberVar (Var v) = zoom (alongside (at v) simple) $ maybe (_2 <<+= 1) return =<< use _1

numberAe :: Monad m => AffineExpression Rational -> StateT NumberState m (Integer, [(PPLDimentionType, Integer)])
numberAe ae = zoom' (with ae) $ mfix' $ \(LCM flcm) -> do
    let norm s = numerator s * (flcm `div` denominator s)
    (lcm', r) <- useMap (_2 . coeff . withIndex) $ \(v, s) -> zoom _1 $ do
        v' <- numberVar v
        return (Option . Just . LCM $ denominator s, [(v' , norm s)])
    (cl, cn) <- (LCM . denominator &&& norm) <$> use (_2 . constant)
    return ((cn, r), maybe cl (cl Data.Semigroup.<>) . getOption $ lcm')

numberCs :: Monad m => Constraints Rational -> StateT NumberState m [(Integer, [(PPLDimentionType, Integer)], ConstraintType)]
numberCs = mapMOf' (constr . each . norm) $ fmap ((:[]) . unwrap) . first' numberAe
           where norm = to (\(l, c, r) -> (l %- r, c))
                 unwrap ((x, y), z) = (x, y, z)

-- | Solve a linear problem.
lpSolve :: (AffineExpressionLike l Rational) => Constraints Rational -> Objective l -> SolutionResult (MIPSolution Rational)
lpSolve cs obj = mipSolve cs obj $! Integers []

-- | Solve a mixed integer problem.
mipSolve :: (AffineExpressionLike l Rational) => Constraints Rational -> Objective l -> Integers -> SolutionResult (MIPSolution Rational)
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

-- Misc
data Comb a b = Zero | One a | Many b

comb Zero e = One e
comb (One a) e = Many $ a %+ e
comb (Many a) e = Many $ a %+ e

class Subst l where
  type family SubstConf l :: * -> *
  subst :: SubstConf l r -> l -> r

data SubstConfLE i o m s r = SubstConfLE { _convVar :: Var -> i,
                                           _scalarMul :: s -> i -> o,
                                           _addOne :: o -> o -> m,
                                           _addMult :: m -> o -> m,
                                           _zero :: r,
                                           _one :: o -> r,
                                           _multi :: m -> r }
data SubstConfAE i o m lr s r = SubstConfAE { _leConf :: SubstConfLE i o m s lr,
                                              _addScalar :: lr -> s -> r }
makeClassy ''SubstConfLE
makeLenses ''SubstConfAE
instance HasSubstConfLE (SubstConfAE i o m lr s r) i o m s lr where
    substConfLE = leConf

data SubstConfLE' s r = forall i o m. SubstConfLE' (SubstConfLE i o m s r)
data SubstConfAE' s r = forall i o m lr. SubstConfAE' (SubstConfAE i o m lr s r)

instance Subst (LinearExpression s) where
  type SubstConf (LinearExpression s) = SubstConfLE' s
  subst sc' l = case sc' of
                  SubstConfLE' sc ->
                    let comb Zero e = One e
                        comb (One a) e = Many $ (sc ^. addOne) a e
                        comb (Many a) e = Many $ (sc ^. addMult) a e
                        (%%*) = sc ^. scalarMul
                        f = sc ^. convVar
                        runComb Zero = sc ^. zero
                        runComb (One a) = sc ^. one $ a
                        runComb (Many a) = sc ^. multi $ a
                    in runComb $ ifoldl (\v a s -> comb a $ s %%* f (Var v)) Zero (l ^. coeff_)

instance Subst (AffineExpression s) where
  type SubstConf (AffineExpression s) = SubstConfAE' s
  subst sc' l = case sc' of
                  SubstConfAE' sc ->
                    (sc ^. addScalar) (subst (SubstConfLE' $ sc ^. substConfLE) (l ^. linearExpression)) (l ^. constant)


