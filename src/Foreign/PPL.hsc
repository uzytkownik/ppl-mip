module Foreign.PPL
(
  ConstraintType(..),
  Objective(..),
  PPLDimentionType,
  SolutionResult(..),
  pplInitialize,
  withMipProblem,
  solve,
  -- Silence warnings
  MPZ(..),
  PPLCoefficient(..),
  PPLLinearExpression(..),
  PPLConstraint(..),
  PPLConstraintSystem(..),
  PPLMIPProblem(..),
  PPLGenerator(..),
)
where
import Control.Exception
import Control.Monad
import Data.Bits
import Data.List
import Data.Ratio
import Data.Typeable
import Data.Word
import Foreign.C
import Foreign.ForeignPtr
import Foreign.Marshal
import Foreign.Ptr
import Foreign.Storable

#include "gmp.h"

foreign import ccall "__gmpz_init" mpz_init :: Ptr MPZ -> IO ()
foreign import ccall "__gmpz_clear" mpz_clear' :: Ptr MPZ -> IO ()
foreign import ccall "__gmpz_get_ui" mpz_get_ui :: Ptr MPZ -> IO CULong
foreign import ccall "__gmpz_add_ui" mpz_add_ui :: Ptr MPZ -> Ptr MPZ -> CULong -> IO ()
foreign import ccall "__gmpz_mul_2exp" mpz_mul_2exp :: Ptr MPZ -> Ptr MPZ -> (#type mp_bitcnt_t) -> IO ()
foreign import ccall "__gmpz_neg" mpz_neg :: Ptr MPZ -> Ptr MPZ -> IO ()
foreign import ccall "__gmpz_tdiv_q_2exp" mpz_tdiv_q_2exp  :: Ptr MPZ -> Ptr MPZ -> (#type mp_bitcnt_t) -> IO ()
foreign import ccall "__gmpz_cmpabs_ui" mpz_cmpabs_ui :: Ptr MPZ -> CULong -> IO CInt

newtype MPZ = MPZ (ForeignPtr MPZ)

_mallocBytes :: Int -> (Ptr a -> IO ()) -> FunPtr (Ptr a -> IO ()) -> IO (ForeignPtr  a)
_mallocBytes s i c = do
  v <- bracketOnError (mallocBytes s) free (newForeignPtr finalizerFree)
  withForeignPtr v $ \v' -> mask_ (i v' >> addForeignPtrFinalizer c v)
  return $! v

_allocBytes :: Int -> (Ptr a -> IO ()) -> (Ptr a -> IO ()) -> (Ptr a -> IO b) -> IO b
_allocBytes s i c f =
  allocaBytes s $ \v -> bracket_ (i v) (c v) (f v)

_allocTag :: (Ptr (Ptr a) -> IO ()) -> (Ptr a -> IO ()) -> (Ptr a -> IO b) -> IO b
_allocTag i c f = bracket (alloca $! \p -> i p >> peek p) c f

allocaMpz :: (Ptr MPZ -> IO a) -> IO a
allocaMpz = _allocBytes (#size mpz_t) mpz_init mpz_clear'

storeIntegerInMpz :: Integer -> Ptr MPZ -> IO ()
storeIntegerInMpz i mpz =
  let ws = unfoldr uws (abs i)
      uws 0 = Nothing
      uws j = Just $! (\(a, b) -> (fromIntegral b, a)) $! divMod j ull
      sh = fromIntegral $! finiteBitSize (0 :: CULong)
      ull = toInteger (maxBound :: CULong) + 1
  in do forM_ (reverse ws) $ \w -> do
          mpz_mul_2exp mpz mpz sh
          mpz_add_ui mpz mpz w
        when (i < 0) $ mpz_neg mpz mpz

withMpzFromInteger :: Integer -> (Ptr MPZ -> IO a) -> IO a
withMpzFromInteger i f = allocaMpz $ \mpz -> storeIntegerInMpz i mpz >> f mpz

loadIntegerFromMpz :: Ptr MPZ -> IO Integer
loadIntegerFromMpz =
  go 0 0
  where go :: Integer -> Int -> Ptr MPZ -> IO Integer
        go acc sh mpz = do
          lsb <- mpz_get_ui mpz
          let acc' = acc + fromIntegral lsb `shiftL` sh
              shift' = finiteBitSize (0 :: CULong)
              cpsign x y
                | y > 0     = x
                | otherwise = -x
              pmpsize :: Ptr MPZ -> IO CInt
              pmpsize = (#peek __mpz_struct, _mp_size)
          cmpabs <- mpz_cmpabs_ui mpz maxBound
          if cmpabs > 0
            then (mpz_tdiv_q_2exp mpz mpz $! fromIntegral shift') >>
                 go acc' (sh + shift') mpz
            else cpsign acc' <$> pmpsize mpz

#include "ppl_c.h"

foreign import ccall "ppl_initialize" ppl_initialize :: IO CInt

data PPLError = OutOfMemory
              | InvalidArgument
              | DomainError
              | LengthArgument
              | ArithmeticOverflow
              | InternalError
              | UnknownStandardException
              | TimeoutException
              | LogicError
              deriving (Typeable, Show)

instance Exception PPLError where {}

pplToException :: CInt -> IO ()
pplToException 0                                   = return ()
pplToException (#const PPL_ERROR_OUT_OF_MEMORY)    = throwIO OutOfMemory
pplToException (#const PPL_ERROR_INVALID_ARGUMENT) = throwIO InvalidArgument
pplToException (#const PPL_ERROR_DOMAIN_ERROR)     = throwIO DomainError
pplToException (#const PPL_ERROR_LENGTH_ERROR)     = throwIO LengthArgument
pplToException (#const PPL_ARITHMETIC_OVERFLOW)    = throwIO ArithmeticOverflow
pplToException (#const PPL_STDIO_ERROR)            = throwErrno "In PPL"
pplToException (#const PPL_ERROR_INTERNAL_ERROR)   = throwIO InternalError
pplToException (#const PPL_ERROR_UNKNOWN_STANDARD_EXCEPTION) =
  throwIO UnknownStandardException
pplToException (#const PPL_TIMEOUT_EXCEPTION)      = throwIO TimeoutException
pplToException (#const PPL_ERROR_LOGIC_ERROR)      = throwIO LogicError
pplToException _                                   = error "Unknown code"

pplInitialize :: IO ()
pplInitialize = pplToException =<< ppl_initialize

foreign import ccall "ppl_new_Coefficient" ppl_new_Coefficient :: Ptr (Ptr PPLCoefficient) -> IO CInt
foreign import ccall "ppl_new_Coefficient_from_mpz_t" ppl_new_Coefficient_from_mpz :: Ptr (Ptr PPLCoefficient) -> Ptr MPZ -> IO CInt
foreign import ccall "ppl_delete_Coefficient" ppl_delete_Coefficient :: Ptr PPLCoefficient -> IO CInt
foreign import ccall "ppl_Coefficient_to_mpz_t" ppl_Coefficient_to_mpz_t :: Ptr PPLCoefficient -> Ptr MPZ -> IO CInt

newtype PPLCoefficient = PPLCoefficient (ForeignPtr PPLCoefficient)

withCoefficient :: Integer -> (Ptr PPLCoefficient -> IO a) -> IO a
withCoefficient i =
  let init' = pplToException <=< withMpzFromInteger i . ppl_new_Coefficient_from_mpz
      clear = pplToException <=< ppl_delete_Coefficient
  in _allocTag init' clear

readCoefficient :: (Ptr PPLCoefficient -> IO a) -> IO (a, Integer)
readCoefficient f =
  let init' = pplToException <=< ppl_new_Coefficient
      clear = pplToException <=< ppl_delete_Coefficient
  in _allocTag init' clear $ \c -> do
    r <- f c
    v <- allocaMpz $ \mpz -> do
      pplToException =<< ppl_Coefficient_to_mpz_t c mpz
      loadIntegerFromMpz mpz
    return $! (r, v)

readCoefficient_ :: (Ptr PPLCoefficient -> IO ()) -> IO Integer
readCoefficient_ f = snd <$> readCoefficient f

foreign import ccall "ppl_new_Linear_Expression_with_dimension" ppl_new_Linear_Expression_with_dimension :: Ptr (Ptr PPLLinearExpression) -> PPLDimentionType -> IO CInt
foreign import ccall "ppl_delete_Linear_Expression" ppl_delete_Linear_Expression :: Ptr PPLLinearExpression -> IO CInt
foreign import ccall "ppl_Linear_Expression_add_to_coefficient" ppl_Linear_Expression_add_to_coefficient :: Ptr PPLLinearExpression -> PPLDimentionType -> Ptr PPLCoefficient -> IO CInt
foreign import ccall "ppl_Linear_Expression_add_to_inhomogeneous" ppl_Linear_Expression_add_to_inhomogeneous:: Ptr PPLLinearExpression -> Ptr PPLCoefficient -> IO CInt

type PPLDimentionType = #type ppl_dimension_type
newtype PPLLinearExpression = PPLLinearExpression (ForeignPtr PPLLinearExpression)

withLinearExpression :: Integer -> [(PPLDimentionType, Integer)] -> (Ptr PPLLinearExpression -> IO a) -> IO a
withLinearExpression ih cs f =
  let dims = (1 +) . maximum . map fst $ cs
      init' = pplToException <=< flip ppl_new_Linear_Expression_with_dimension dims
      clear = pplToException <=< ppl_delete_Linear_Expression
  in _allocTag init' clear $ \le -> do
      forM_ cs $ \(dim, val) -> withCoefficient val $ \val' ->
        pplToException =<< ppl_Linear_Expression_add_to_coefficient le dim val'
      withCoefficient (negate ih) $ \val' ->
        pplToException =<< ppl_Linear_Expression_add_to_inhomogeneous le val'
      f le

#def typedef enum ppl_enum_Constraint_Type __hs_ppl_enum_Constraint_Type;
type PPLConstraintType = #type __hs_ppl_enum_Constraint_Type

foreign import ccall "ppl_new_Constraint" ppl_new_Constraint :: Ptr (Ptr PPLConstraint) -> Ptr PPLLinearExpression -> PPLConstraintType -> IO CInt
foreign import ccall "ppl_delete_Constraint" ppl_delete_Constraint :: Ptr PPLConstraint -> IO CInt

data ConstraintType = LessThan
                    | LessOrEqual
                    | Equal
                    | GreaterOrEqual
                    | GreaterThan deriving (Eq,Show,Typeable)

ctToInt :: ConstraintType -> PPLConstraintType
ctToInt LessThan       = #const PPL_CONSTRAINT_TYPE_LESS_THAN
ctToInt LessOrEqual    = #const PPL_CONSTRAINT_TYPE_LESS_OR_EQUAL
ctToInt Equal          = #const PPL_CONSTRAINT_TYPE_EQUAL
ctToInt GreaterOrEqual = #const PPL_CONSTRAINT_TYPE_GREATER_OR_EQUAL
ctToInt GreaterThan    = #const PPL_CONSTRAINT_TYPE_GREATER_THAN

newtype PPLConstraint = PPLConstraint (ForeignPtr PPLConstraint)

withConstraint :: Integer -> [(PPLDimentionType, Integer)] -> ConstraintType -> (Ptr PPLConstraint -> IO a) -> IO a
withConstraint ih cs ct =
  let init' = (\cst -> withLinearExpression ih cs $ \le ->
                ppl_new_Constraint cst le (ctToInt ct)) >=>
              pplToException
      clear = pplToException <=< ppl_delete_Constraint
  in _allocTag init' clear

foreign import ccall "ppl_new_Constraint_System" ppl_new_Constraint_System :: Ptr (Ptr PPLConstraintSystem) -> IO CInt
foreign import ccall "ppl_delete_Constraint_System" ppl_delete_Constraint_System :: Ptr PPLConstraintSystem -> IO CInt
foreign import ccall "ppl_Constraint_System_insert_Constraint" ppl_Constraint_System_insert_Constraint :: Ptr PPLConstraintSystem -> Ptr PPLConstraint -> IO CInt

newtype PPLConstraintSystem = PPLConstraintSystem (ForeignPtr PPLConstraintSystem)

type PPLConstraintDesc = (Integer, [(PPLDimentionType, Integer)], ConstraintType)

withConstraintSystem :: [PPLConstraintDesc] -> (Ptr PPLConstraintSystem -> IO a) -> IO a
withConstraintSystem css f =
  let init' = pplToException <=< ppl_new_Constraint_System
      clear = pplToException <=< ppl_delete_Constraint_System
      uncurry3 g (x, y, z) = g x y z
  in _allocTag init' clear $ \cs -> do
    forM_ css $ flip (uncurry3 withConstraint) $ \ct ->
      pplToException =<< ppl_Constraint_System_insert_Constraint cs ct
    f cs

foreign import ccall "ppl_new_MIP_Problem" ppl_new_MIP_Problem :: Ptr (Ptr PPLMIPProblem) -> PPLDimentionType -> Ptr PPLConstraintSystem -> Ptr PPLLinearExpression -> CInt -> IO CInt
foreign import ccall "ppl_delete_MIP_Problem" ppl_delete_MIP_Problem :: Ptr PPLMIPProblem -> IO CInt
foreign import ccall "ppl_MIP_Problem_add_to_integer_space_dimensions" ppl_MIP_Problem_add_to_integer_space_dimensions :: Ptr PPLMIPProblem -> Ptr PPLDimentionType -> CSize -> IO CInt
foreign import ccall "ppl_MIP_Problem_solve" ppl_MIP_Problem_solve :: Ptr PPLMIPProblem -> IO CInt

foreign import ccall "&PPL_OPTIMIZATION_MODE_MAXIMIZATION" pPL_OPTIMIZATION_MODE_MAXIMIZATION :: Ptr CInt
foreign import ccall "&PPL_OPTIMIZATION_MODE_MINIMIZATION" pPL_OPTIMIZATION_MODE_MINIMIZATION :: Ptr CInt
foreign import ccall "&PPL_MIP_PROBLEM_STATUS_UNFEASIBLE" pPL_MIP_PROBLEM_STATUS_UNFEASIBLE :: Ptr CInt
foreign import ccall "&PPL_MIP_PROBLEM_STATUS_UNBOUNDED" pPL_MIP_PROBLEM_STATUS_UNBOUNDED :: Ptr CInt
foreign import ccall "&PPL_MIP_PROBLEM_STATUS_OPTIMIZED" pPL_MIP_PROBLEM_STATUS_OPTIMIZED :: Ptr CInt

newtype PPLMIPProblem = PPLMIPProblem (ForeignPtr PPLMIPProblem)

-- | Objective function (either minimizes or maximizes)
data Objective o = Maximize o | Minimize o

instance Functor Objective where
  f `fmap` Maximize v = Maximize $! f v
  f `fmap` Minimize v = Minimize $! f v

instance Foldable Objective where
  foldMap f (Maximize v) = f v
  foldMap f (Minimize v) = f v

instance Traversable Objective where
  traverse f (Maximize v) = Maximize <$> f v
  traverse f (Minimize v) = Minimize <$> f v

-- | Result of MIP problem
data SolutionResult a = Unfeasable | Unbounded | Optimized a deriving (Eq,Show)

instance Functor SolutionResult where
  _ `fmap` Unfeasable = Unfeasable
  _ `fmap` Unbounded = Unbounded
  f `fmap` (Optimized s) = Optimized $! f s

objectiveToInt :: Objective o -> IO CInt
objectiveToInt (Maximize _) = peek pPL_OPTIMIZATION_MODE_MAXIMIZATION
objectiveToInt (Minimize _) = peek pPL_OPTIMIZATION_MODE_MINIMIZATION

fromObjective :: Objective o -> o
fromObjective (Maximize o) = o
fromObjective (Minimize o) = o

solutionFromInt :: CInt -> IO a -> IO (SolutionResult a)
solutionFromInt i f = do
  unfeasable <- peek pPL_MIP_PROBLEM_STATUS_UNFEASIBLE
  unbounded <- peek pPL_MIP_PROBLEM_STATUS_UNBOUNDED
  optimized <- peek pPL_MIP_PROBLEM_STATUS_OPTIMIZED
  case () of
    () | i == unfeasable -> return $! Unfeasable
       | i == unbounded  -> return $! Unbounded
       | i == optimized  -> Optimized <$> f
       | otherwise       -> error "Unknown return code"

withMipProblem :: PPLDimentionType
               -> [PPLConstraintDesc]
               -> Objective (Integer, [(PPLDimentionType, Integer)])
               -> [PPLDimentionType]
               -> (Ptr PPLMIPProblem -> IO a) -> IO a
withMipProblem dim css obj is f =
  withConstraintSystem css $ \cs' ->
  let (ih, cs) = fromObjective obj
  in withLinearExpression ih cs $ \le ->
  let init' mip =
        objectiveToInt obj >>= \m' ->
        ppl_new_MIP_Problem mip dim cs' le m' >>=
        pplToException
      clear = pplToException <=< ppl_delete_MIP_Problem
  in _allocTag init' clear $ \mip -> do
      withArrayLen is $ \isl is' ->
        let isl' = fromIntegral isl
        in ppl_MIP_Problem_add_to_integer_space_dimensions mip is' isl' >>=
           pplToException
      f mip

foreign import ccall "ppl_MIP_Problem_optimizing_point" ppl_MIP_Problem_optimizing_point :: Ptr PPLMIPProblem -> Ptr (Ptr PPLGenerator) -> IO CInt
foreign import ccall "ppl_Generator_coefficient" ppl_Generator_coefficient :: Ptr PPLGenerator -> PPLDimentionType -> Ptr PPLCoefficient -> IO CInt
foreign import ccall "ppl_Generator_divisor" ppl_Generator_divisor :: Ptr PPLGenerator -> Ptr PPLCoefficient -> IO CInt

newtype PPLGenerator = PPLGenerator (ForeignPtr PPLGenerator)

solve :: PPLDimentionType -> Ptr PPLMIPProblem -> IO (SolutionResult [Rational])
solve n mip = do
  res <- ppl_MIP_Problem_solve mip
  solutionFromInt res $ alloca $ \gen' -> do
    pplToException =<< ppl_MIP_Problem_optimizing_point mip gen'
    gen <- peek gen'
    d <- readCoefficient_ $ pplToException <=< ppl_Generator_divisor gen
    forM [0..n-1] $ \i ->
      (% d) <$> (readCoefficient_ $ pplToException <=< ppl_Generator_coefficient gen i)
