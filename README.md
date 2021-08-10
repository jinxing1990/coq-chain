# (Auto)Complete this Proof:Decentralized Proof Generation via Smart Contracts

Code for the proof of concept presented in the paper:  

Title: (Auto)Complete this Proof:Decentralized Proof Generation via Smart Contracts   
Authors: [Jin Xing Lim](https://www.linkedin.com/in/jin-xing-lim-840814189/), [Barnabé Monnot](https://barnabemonnot.com/), [Georgios Piliouras](https://people.sutd.edu.sg/~georgios/) and [Shaowei Lin](https://shaoweilin.github.io/)   
Conference: [6th Conference on Artificial Intelligence and Theorem Proving (AITP 2021)](http://aitp-conference.org/2021/)

For potential bugs, please open an issue.   
For any other questions, please ask in Discussions.

## Dependencies between contributions

The "contributions" folder contains Coq files that eventually leads to different formal proofs of the theorem type `sort_prog`:
```coq
Theorem sort_prog : forall (l : list nat), {l' : list nat | sorted l' /\ permutation l' l}.
```

> **NOTE:** The original and full documentation of formalization of different variations of divide-and-conquer algorithm design paradigm for lists and the different sorting algorithms' proofs and programs can be found on https://github.com/jinxing1990/coq-formalized-divide-and-conquer.

The following are the dependencies between the Coq files that lead to different proofs of the theorem type `sort_prog`:

--- 
**LEGENDS:**

Edge: Type  
Node (black): Contribution from human prover   
Node (green): Contribution from AI System (CoqHammer)   

---

1. Insertion Sort:

![Insertion Sort](/images/isort_dep.png)

2. Merge Sort:

![Merge Sort](/images/msort_dep.png)

3. Pair Sort:

![Pair Sort](/images/psort_dep.png)

4. Quick Sort:

![Quick Sort](/images/qsort_dep.png)

Additional contributions/Coq files that are not included in any of the images above:

ct04.v: Formalization of new induction princple/tactic `div_conq_split` 
ct11.v: Connect all the dependent contributions of the proof via `induction` and extract as Ocaml programs (insert_prog, isort_prog)    
ct16.v: Formalization of new induction princple/tactic `div_conq_pair`
ct18.v: Connect all the dependent contributions of the proof via `div_conq_split` and extract as Ocaml programs (merge, msort_prog)
ct21.v: Connect all the dependent contributions of the proof via `div_conq_pair` and extract as Ocaml programs (psort_prog)
ct22.v: Formalization of new induction princple/tactic `div_conq_pivot`
ct26.v: Connect all the dependent contributions of the proof via `div_conq_pivot` and extract as Ocaml programs (qsort_prog)

## Prerequitses

1. Coq Version 8.12
2. OCaml [most versions will work] (if you would like to test the extracted files)
3. CoqHammer

    Just need to install coq-hammer-tactics:
    ```
    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam install coq-hammer-tactics
    ```

## Make and compile all files

1. Go to the "coq-chain" folder.
2. Run the Makefile in terminal with the following command:
    ```
    $ make
    ```
3. To test the extracted files, run the following command in terminal:
    ```
    $ make test_extraction
    ```
> NOTE: To clean all compiled files, run the following command in terminal: ` $ make clean`.