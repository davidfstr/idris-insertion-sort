# idris-insertion-sort

This is a provably correct implementation of insertion sort in Idris.

Specifically, it is an implementation of the following function definition:

```
insertionSort :
    Ord e =>
    (xs:Vect n e) ->
    (xs':Vect n e ** (IsSorted xs', ElemsAreSame xs xs'))
```

Given a list of elements, this function will return:

1. an output list,
2. an `IsSorted` proof that the output list is sorted, and
3. an `ElemsAreSame` proof that the input list and output lists contain
   the same elements.

This program makes heavy use of proof terms, a special facility only available
in dependently-typed programming languages like Idris.

## Prerequisites

* Idris 1.3.1 or later
    - Probably any Idris 1.x will work.
* Make

## How to Run

```
make run
```

## Example Output

```
$ make run
idris -o InsertionSort InsertionSort.idr
./InsertionSort
Please type a space-separated list of integers: 
3 2 1
After sorting, the integers are: 
1 2 3
```

## See the Proof Term!

Another way to run the program is to run it directly using the Idris
interpreter. The advantage here is that you can see not just the resulting
sorted output list but also the resulting proof terms of the algorithm.

```
$ idris --nobanner InsertionSort.idr
*InsertionSort> insertionSort [2,1]
MkSigma [1, 2]
        (IsSortedMany 1 2 [] Oh (IsSortedOne 2),
         SamenessIsTransitive (PrependXIsPrependX 2
                                                  (SamenessIsTransitive (PrependXIsPrependX 1
                                                                                            NilIsNil)
                                                                        (PrependXIsPrependX 1
                                                                                            NilIsNil)))
                              (PrependXYIsPrependYX 2
                                                    1
                                                    NilIsNil)) : Sigma (Vect 2
                                                                             Integer)
                                                                       (\xs' =>
                                                                          (IsSorted xs',
                                                                           ElemsAreSame [2,
                                                                                         1]
                                                                                        xs'))
```

## License

Copyright (c) 2015 by David Foster
