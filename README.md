# Big step normalisation

This is an evaluator and a normalisation function for a simple type theory, following 
[Big-Step Normalisation [Altenkirch, Chapman]]
(http://www.cs.nott.ac.uk/~psztxa/publ/jtait07.pdf).

### modules
- Syntax:               definition of the QIIT syntax of type theory, and associated lemmas.
- Variable:             definition of variables and renamings (weakenings)
- Values:               definition of syntactic values and associated lemmas
- Normal forms:         definition of normal forms and associated lemmas
- Evaluator:            definition of the big step normalisation relation
- TypeEvaluator:        definition of substitution-free types, and evaluation of type
- StrongComputability:  definition of the strong computability predicate on values, with quote/unquote lemmas
- BSN:                  main proofs of correction of BSN (termination, stability)
