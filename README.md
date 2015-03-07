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

* Idris 0.9.16
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

## License

Copyright (c) 2015 by David Foster
