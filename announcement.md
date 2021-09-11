
In this homework assignment we will focus on mergesort and try to implement part of it in Dafny and verify its correctness. We will focus on the `merge` part of mergesort.

The assignment includes (i) formalizing the logical specifications in Dafny, i.e., what does it mean for the code to be correct, and (ii) using Dafny to verify that an implementation satisfies the specification.

We start by giving an english specification of the `merge` method of mergesort.

> The `merge` method of mergesort, takes two disjoint and already sorted array slices and _merges_ them into a single array slice that is _sorted_.

Your implementation of `merge` should be based on the following pseudocode implementation (taken from Wikipedia).

```
// Left  source half is A[ iBegin:iMiddle-1].
// Right source half is A[iMiddle:iEnd-1   ].
// Result is            B[ iBegin:iEnd-1   ].
void TopDownMerge(A[], iBegin, iMiddle, iEnd, B[])
{
    i = iBegin, j = iMiddle;
 
    // While there are elements in the left or right runs...
    for (k = iBegin; k < iEnd; k++) {
        // If left run head exists and is <= existing right run head.
        if (i < iMiddle && (j >= iEnd || A[i] <= A[j])) {
            B[k] = A[i];
            i = i + 1;
        } else {
            B[k] = A[j];
            j = j + 1;
        }
    }
}
```

You are free to modify it accordingly in order to verify it, but do not modify it so much that it becomes trivial, i.e., ending up with a method that simply copies both array slices and then sorts the combined array.

### Part 1

In order to familiarize with `merge` and Dafny we first only focus on the `sorted` postcondition of the `merge` specification. 
Fill in the necessary preconditions, implement, and verify `merge`, the signature of which is shown below. 

```dafny
method mergeSimple(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>)
    modifies b
    requires ...

    ensures sorted(b, start, end)
{
    ...
}
```

Note 1: The signature uses two separate sequences instead of a single input array (as the wikipedia implementation) for simplicity.

Note 2: You might need some auxiliary state to ensure that after the loop we end up with a sorted `b`.

### Part 2

We will now verify the complete `merge` where we are also interested in the resulting array being a merge of the other two, meaning that it contains exactly the elements contained in the original two arrays.
The signature follows:

```dafny
method merge(a1: seq<int>, a2: seq<int>, start: int, end: int, b: array<int>) returns (aux_state: ...)
    modifies b

    ensures sorted(b, start, end)
    ensures ...
    ensures merged(a1, a2, b, ...)
{
    ...
}
```

Fill in the necessary preconditions, implement, and verify `merge`.

You might need additional auxiliary state to establish a relation between the two input sequences and the output array.

Most of the code and predicates from part 1 can be reused. You will probably need to modify your implementation depending on the new auxiliary state.

### Part 3 (Optional)

Optionally, if you are interested in diving deeper in Dafny, you could verify the following pseudocode implementation of a complete mergesort (again taken from Wikipedia).
Since this part is optional, feel free to use any mergesort implementation that you want as long as it uses the `merge` that you implemented above (referred to as `TopDownMerge` in the following pseudocode).

```
// Split A[] into 2 runs, sort both runs into B[], merge both runs from B[] to A[]
// iBegin is inclusive; iEnd is exclusive (A[iEnd] is not in the set).
void TopDownSplitMerge(B[], iBegin, iEnd, A[])
{
    if (iEnd - iBegin <= 1)                     // if run size == 1
        return;                                 //   consider it sorted
    // split the run longer than 1 item into halves
    iMiddle = (iEnd + iBegin) / 2;              // iMiddle = mid point
    // recursively sort both runs from array A[] into B[]
    TopDownSplitMerge(A, iBegin,  iMiddle, B);  // sort the left  run
    TopDownSplitMerge(A, iMiddle,    iEnd, B);  // sort the right run
    // merge the resulting runs from array B[] into A[]
    TopDownMerge(B, iBegin, iMiddle, iEnd, A);
}
```

Note that Dafny performs modular verification, meaning that it will _ignore_ the implementation of `merge` and only assume that `merge` postconditions hold if its preconditions hold. This means that you might need to strengthen the postconditions of `merge` (by extending its postconditions) to successfully verify that `TopDownSplitMerge` returns a sorted and merged array.

Hint: You might need to specify that some of your methods do not modify arbitrary parts of their argument arrays. This page might be helpful (http://leino.science/papers/krml273.html).

### Hints

- It is important when working with solvers and automated provers that the verification problem is extremely hard in general, and therefore many times it might be neccessary to modify the specification or implementation to do the same thing in a slightly different fashion in order to satisfy the prover. 

- Sequences in Dafny are easier to work with than arrays, i.e., reasoning about their slices is easier since it doesn't require refering to indices, so it might be good to write most specifications using them.

- When a method doesn't verify (will happen often :) ), try to break it down to smaller pieces, or start adding assertions to figure out what is wrong. Dafny does try to give a counterexample often, but it is not always adequate for debugging purposes.

