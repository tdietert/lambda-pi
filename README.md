# lambda-pi 

This project is a toy implementation of the dependently typed lambda calculus
known as λ<sub>Π</sub>, based on the language and semantics presented in the 
paper [A tutorial implementation of a dependently typed lambda
calculus](https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf), by Loh, McBride,
and Swierstra. Instead of the ad-hoc implementation of de Bruijn indices 
presented in the paper, we use the library [`unbound-generics`](https://hackage.haskell.org/package/unbound)
for alpha equivalence and capture-avoiding substitution (CAS) of lambda 
abstractions and pi terms. This project hopes to explore the implementation
details of compiling dependently typed programming languages.
