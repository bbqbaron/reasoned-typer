# pie

An attempt to learn both minikanren a la [The Reasoned Schemer](https://mitpress.mit.edu/books/reasoned-schemer) and Pie from [The Little Typer](https://mitpress.mit.edu/books/little-typer) at the same time by encoding Pie's typechecking rules in Clojure's core.logic (which is hopefully close enough to minikanren to qualify).

It turns out this has [come up before](https://icfp18.sigplan.org/details/scheme-2018-papers/7/A-Surprisingly-Competitive-Conditional-Operator-miniKanrenizing-the-Inference-Rules-), thought I deliberately haven't watched the talk yet, to insulate myself.

The first pass was to encode the rules as literally and naively as possible, transcribing Pie's rules directly into minikanren where possible. As a result, there are certainly many typechecking failures that will result in infinite or near-infinite searches!

## License 

See [LICENSE](LICENSE)

