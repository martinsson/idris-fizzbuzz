module FizzBuzz

%default total

data IsDivisibleBy : (divisor : Nat) -> (nz_proof : Not (divisor = 0)) -> (dividend : Nat) -> Type where
  MkIsDivisibleBy :  (divisor : Nat)
                  -> (dividend : Nat)
                  -> (prf : modNatNZ dividend divisor nz_proof = 0 )
                  -> IsDivisibleBy divisor nz_proof dividend


extractPrf : IsDivisibleBy divisor nz_proof dividend -> (modNatNZ dividend divisor nz_proof  = 0)
extractPrf (MkIsDivisibleBy dividend divisor prf) = prf


isDivisibleByNZ : (divisor : Nat) -> {auto nz_proof : Not (divisor = Z)} -> (dividend : Nat) -> Dec (IsDivisibleBy divisor nz_proof dividend)
isDivisibleByNZ Z     dividend { nz_proof}     = void (nz_proof Refl)
isDivisibleByNZ (S k) dividend { nz_proof } with (decEq (modNatNZ dividend (S k) nz_proof) Z)
  isDivisibleByNZ (S k) dividend | (Yes isdiv) = Yes (MkIsDivisibleBy (S k) dividend isdiv)
  isDivisibleByNZ (S k) dividend | (No contra) = No $ contra . extractPrf


IsFizz : Nat -> Type
IsFizz = IsDivisibleBy 3 absurd

IsBuzz : Nat -> Type
IsBuzz = IsDivisibleBy 5 absurd


isFizz : (k : Nat) -> Dec (IsFizz k)
isFizz = isDivisibleByNZ 3 { nz_proof = absurd }

isBuzz : (k : Nat) -> Dec (IsBuzz k)
isBuzz = isDivisibleByNZ 5 { nz_proof = absurd }

data FizzBuzzT : (k : Nat) -> Type where
  Fizz     : (k : Nat) -> IsFizz k       -> Not (IsBuzz k) -> FizzBuzzT k
  Buzz     : (k : Nat) -> Not (IsFizz k) -> IsBuzz k       -> FizzBuzzT k
  FizzBuzz : (k : Nat) -> IsFizz k       -> IsBuzz k       -> FizzBuzzT k
  Number   : (k : Nat) -> Not (IsFizz k) -> Not (IsBuzz k) -> FizzBuzzT k

fizzBuzz : (k : Nat) -> FizzBuzzT k
fizzBuzz k
    = case (isFizz k, isBuzz k) of
           (Yes isFizzProof, No isNotBuzzProof) =>  Fizz k isFizzProof isNotBuzzProof
           (No isNotFizzProof, Yes isBuzzProof) => Buzz k isNotFizzProof isBuzzProof
           (Yes isFizzProof, Yes isBuzzProof) => FizzBuzz k isFizzProof isBuzzProof
           (No isNotFizzProof, No isNotBuzzProof) => Number k isNotFizzProof isNotBuzzProof


showFizzBuzz : Nat -> String
showFizzBuzz k = case fizzBuzz k of
                  Fizz k _ _     => "fizz"
                  Buzz k _ _     => "buzz"
                  FizzBuzz k _ _ => "fizzbuzz"
                  Number k _ _   => show k
