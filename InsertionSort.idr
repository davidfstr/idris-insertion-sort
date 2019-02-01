import Data.So
import Data.Vect

--------------------------------------------------------------------------------
-- Utility

-- Makes a best effort to return an error message.
-- Use this only on code paths that you can deduce should be unreachable. 
unsafeError : String -> a
unsafeError message = believe_me message

-- Unwraps a `Just a` to a plain `a`.
-- Useful for command-line debugging but unsafe for general program usage.
unsafeUnwrapJust : (Maybe a) -> a
unsafeUnwrapJust (Just x) =
    x
unsafeUnwrapJust (Nothing) =
    unsafeError "The specified Maybe was not a Just."

--------------------------------------------------------------------------------
-- IsLte

-- Proof that `x <= y`.
IsLte : Ord e => (x:e) -> (y:e) -> Type
IsLte x y = So (x <= y)

mkIsLte : Ord e => (x:e) -> (y:e) -> Maybe (IsLte x y)
mkIsLte x y =
    case choose (x <= y) of 
        Left proofXLteY =>
            Just proofXLteY
        Right proofNotXLteY =>
            Nothing

-- Given an `x` and a `y`, returns a proof that either `x <= y` or `y <= x`.
chooseLte :
    Ord e => 
    (x:e) -> (y:e) -> 
    Either (IsLte x y) (IsLte y x)
chooseLte x y =
    case choose (x <= y) of 
        Left proofXLteY =>
            Left proofXLteY
        Right proofNotXLteY =>
            -- Given: not (x <= y)
            -- Derive: x > y
            -- Derive: y < x
            -- Derive: y <= x
            --
            -- Unfortunately Ord doesn't guarantee the preceding
            -- even though any sane implementation will conform
            -- to those rules. 
            case choose (y <= x) of 
                Left proofYLteX =>
                    Right proofYLteX
                Right proofNotYLteX =>
                    unsafeError "Impossible with a sane Ord implementation."

--------------------------------------------------------------------------------
-- IsSorted

-- Proof that `xs` is sorted.
data IsSorted : (xs:Vect n e) -> Type where
    IsSortedZero :
        IsSorted Nil
    IsSortedOne  :
        Ord e =>
        (x:e) ->
        IsSorted (x::Nil)
    IsSortedMany :
        Ord e => 
        (x:e) -> (y:e) -> (ys:Vect n'' e) ->    -- (n'' == (n - 2))
        (IsLte x y) -> IsSorted (y::ys) ->
        IsSorted (x::(y::ys))

mkIsSorted : Ord e => (xs:Vect n e) -> Maybe (IsSorted xs)
mkIsSorted Nil =
    Just IsSortedZero
mkIsSorted (x::Nil) =
    Just (IsSortedOne x)
mkIsSorted (x::(y::ys)) =
    case (mkIsLte x y) of
        Just proofXLteY =>
            case (mkIsSorted (y::ys)) of
                Just proofYYsIsSorted =>
                    Just (IsSortedMany x y ys proofXLteY proofYYsIsSorted)
                Nothing =>
                    Nothing
        Nothing =>
            Nothing

--------------------------------------------------------------------------------
-- ElemsAreSame

-- Proof that set `xs` and set `ys` contain the same elements.
data ElemsAreSame : (xs:Vect n e) -> (ys:Vect n e) -> Type where
    NilIsNil : 
        ElemsAreSame Nil Nil
    PrependXIsPrependX :
        (x:e) -> ElemsAreSame zs zs' ->
        ElemsAreSame (x::zs) (x::zs')
    PrependXYIsPrependYX :
        (x:e) -> (y:e) -> ElemsAreSame zs zs' ->
        ElemsAreSame (x::(y::zs)) (y::(x::(zs')))
    -- NOTE: Probably could derive this last axiom from the prior ones
    SamenessIsTransitive :
        ElemsAreSame xs zs -> ElemsAreSame zs ys ->
        ElemsAreSame xs ys

XsIsXs : (xs:Vect n e) -> ElemsAreSame xs xs
XsIsXs Nil =
    NilIsNil
XsIsXs (x::ys) =
    PrependXIsPrependX x (XsIsXs ys)

flip : ElemsAreSame xs ys -> ElemsAreSame ys xs
flip NilIsNil =
    NilIsNil
flip (PrependXIsPrependX x proofXsTailIsYsTail) =
    PrependXIsPrependX x (flip proofXsTailIsYsTail)
flip (PrependXYIsPrependYX x y proofXsLongtailIsYsLongtail) =
    PrependXYIsPrependYX y x (flip proofXsLongtailIsYsLongtail)
flip (SamenessIsTransitive proofXsIsZs proofZsIsYs) =
    let proofYsIsZs = flip proofZsIsYs in
    let proofZsIsXs = flip proofXsIsZs in
    let proofYsIsXs = SamenessIsTransitive proofYsIsZs proofZsIsXs in
    proofYsIsXs

-- NOTE: Needed to explicitly pull out the {x}, {y}, {zs}, {us} implicit parameters.
swapFirstAndSecondOfLeft : ElemsAreSame (x::(y::zs)) us -> ElemsAreSame (y::(x::zs)) us
swapFirstAndSecondOfLeft {x} {y} {zs} {us} proofXYZsIsUs =
    let proofYXZsIsXYZs = PrependXYIsPrependYX y x (XsIsXs zs) in
    let proofYZZsIsUs = SamenessIsTransitive proofYXZsIsXYZs proofXYZsIsUs in
    proofYZZsIsUs

--------------------------------------------------------------------------------
-- HeadIs, HeadIsEither

-- Proof that the specified vector has the specified head.
data HeadIs : Vect n e -> e -> Type where
    MkHeadIs : HeadIs (x::xs) x

-- Proof that the specified vector has one of the two specified heads.
-- 
-- NOTE: Could implement this as an `Either (HeadIs xs x) (HeadIs xs y)`,
--       but an explicit formulation feels cleaner.
data HeadIsEither : Vect n e -> (x:e) -> (y:e) -> Type where
    HeadIsLeft  : HeadIsEither (x::xs) x y
    HeadIsRight : HeadIsEither (x::xs) y x

--------------------------------------------------------------------------------
-- Insertion Sort

-- Inserts an element into a non-empty sorted vector, returning a new
-- sorted vector containing the new element plus the original elements.
insert' :
    Ord e =>
    (xs:Vect (S n) e) -> (y:e) -> (IsSorted xs) -> (HeadIs xs x) ->
    (xs':(Vect (S (S n)) e) ** ((IsSorted xs'), (HeadIsEither xs' x y), (ElemsAreSame (y::xs) xs')))
insert' (x::Nil) y (IsSortedOne x) MkHeadIs =
    case (chooseLte x y) of
        Left proofXLteY =>
            let yXNilSameXYNil = PrependXYIsPrependYX y x (XsIsXs Nil) in
            (x::(y::Nil) **
             (IsSortedMany x y Nil proofXLteY (IsSortedOne y),
              HeadIsLeft,
              yXNilSameXYNil))
        Right proofYLteX =>
            let yXNilSameYXNil = XsIsXs (y::(x::Nil)) in
            (y::(x::Nil) ** 
             (IsSortedMany y x Nil proofYLteX (IsSortedOne x),
              HeadIsRight,
              yXNilSameYXNil))
insert' (x::(y::ys)) z proofXYYsIsSorted MkHeadIs =
    case proofXYYsIsSorted of
        (IsSortedMany x y ys proofXLteY proofYYsIsSorted) =>
            case (chooseLte x z) of
                Left proofXLteZ =>
                    -- x::(insert' (y::ys) z)
                    let proofHeadYYsIsY = the (HeadIs (y::ys) y) MkHeadIs in
                    case (insert' (y::ys) z proofYYsIsSorted proofHeadYYsIsY) of
                        -- rest == (_::tailOfRest)
                        ((y::tailOfRest) ** (proofRestIsSorted, HeadIsLeft, proofZYYsSameRest)) =>
                            let proofXZYYsIsXRest = PrependXIsPrependX x proofZYYsSameRest in
                            let proofZXYYsIsXRest = swapFirstAndSecondOfLeft proofXZYYsIsXRest in
                            (x::(y::tailOfRest) **
                             (IsSortedMany x y tailOfRest proofXLteY proofRestIsSorted,
                              HeadIsLeft,
                              proofZXYYsIsXRest))
                        ((z::tailOfRest) ** (proofRestIsSorted, HeadIsRight, proofZYYsSameRest)) =>
                            let proofXZYYsIsXRest = PrependXIsPrependX x proofZYYsSameRest in
                            let proofZXYYsIsXRest = swapFirstAndSecondOfLeft proofXZYYsIsXRest in
                            (x::(z::tailOfRest) **
                             (IsSortedMany x z tailOfRest proofXLteZ proofRestIsSorted,
                              HeadIsLeft,
                              proofZXYYsIsXRest))
                Right proofZLteX =>
                    -- z::(x::(y::ys))
                    let proofZXYYsIsZXYYs = XsIsXs (z::(x::(y::ys))) in
                    (z::(x::(y::ys)) **
                     (IsSortedMany z x (y::ys) proofZLteX proofXYYsIsSorted,
                      HeadIsRight,
                      proofZXYYsIsZXYYs))

-- Inserts an element into a sorted vector, returning a new
-- sorted vector containing the new element plus the original elements.
insert :
    Ord e =>
    (xs:Vect n e) -> (y:e) -> (IsSorted xs) -> 
    (xs':(Vect (S n) e) ** ((IsSorted xs'), (ElemsAreSame (y::xs) xs')))
insert Nil y IsSortedZero =
    ([y] ** (IsSortedOne y, XsIsXs [y]))
insert (x::xs) y proofXXsIsSorted =
    let proofHeadOfXXsIsX = the (HeadIs (x::xs) x) MkHeadIs in
    case (insert' (x::xs) y proofXXsIsSorted proofHeadOfXXsIsX) of
        (xs' ** (proofXsNewIsSorted, proofHeadXsNewIsXOrY, proofYXXsIsXsNew)) =>
            (xs' ** (proofXsNewIsSorted, proofYXXsIsXsNew))

-- Sorts the specified vector,
-- returning a new sorted vector with the same elements.
insertionSort :
    Ord e =>
    (xs:Vect n e) ->
    (xs':Vect n e ** (IsSorted xs', ElemsAreSame xs xs'))
insertionSort Nil =
    (Nil ** (IsSortedZero, NilIsNil))
insertionSort (x::ys) =
    case (insertionSort ys) of
        (ysNew ** (proofYsNewIsSorted, proofYsIsYsNew)) =>
            case (insert ysNew x proofYsNewIsSorted) of
                (result ** (proofResultIsSorted, proofXYsNewIsResult)) =>
                    let proofXYsIsXYsNew = PrependXIsPrependX x proofYsIsYsNew in
                    let proofXYsIsResult = SamenessIsTransitive proofXYsIsXYsNew proofXYsNewIsResult in
                    (result ** (proofResultIsSorted, proofXYsIsResult))

--------------------------------------------------------------------------------
-- Main

-- Parses an integer from a string, returning 0 if there is an error.
parseInt : String -> Integer
parseInt s =
    the Integer (cast s)

-- Joins a list of elements with the provided separator,
-- returning a separator-separated string.
intercalate : Show e => (xs:Vect n e) -> (sep:String) -> String
intercalate Nil sep =
    ""
intercalate (x::Nil) sep =
    show x
intercalate (x::(y::zs)) sep =
    (show x) ++ sep ++ (intercalate (y::zs) sep)

main : IO ()
main = do
    putStrLn "Please type a space-separated list of integers: "
    csv <- getLine
    let numbers = map parseInt (words csv)
    let (sortedNumbers ** (_, _)) = insertionSort (fromList numbers)
    putStrLn "After sorting, the integers are: "
    putStrLn (intercalate sortedNumbers " ")

--------------------------------------------------------------------------------
