# ZET
Nested sets with Cartesian products and a lot of arithmetical functions.

{ 0 1 2 } { 0 1 } cartprod zdup cr zet.

{(2,1),(2,0),(1,1),(1,0),(0,1),(0,0)} ok

powerset zdup cr zet.

{0,{(2,1)},{(2,0)},{(2,1),(2,0)},{(1,1)},{(2,1),(1,1)},{(2,0),(1,1)},{(2,1),(2,0),(1,1)},{(1,0)},{(2,1),(1,0)},{(2,0),(1,0)},{(2,1),(2,0),(1,0)},{(1,1),(1,0)},{(2,1),(1,1),(1,0)},{(2,0),(1,1),(1,0)},{(2,1),(2,0),(1,1),(1,0)},{(0,1)},{(2,1),(0,1)},{(2,0),(0,1)},{(2,1),(2,0),(0,1)},{(1,1),(0,1)},{(2,1),(1,1),(0,1)},{(2,0),(1,1),(0,1)},{(2,1),(2,0),(1,1),(0,1)},{(1,0),(0,1)},{(2,1),(1,0),(0,1)},{(2,0),(1,0),(0,1)},{(2,1),(2,0),(1,0),(0,1)},{(1,1),(1,0),(0,1)},{(2,1),(1,1),(1,0),(0,1)},{(2,0),(1,1),(1,0),(0,1)},{(2,1),(2,0),(1,1),(1,0),(0,1)},{(0,0)},{(2,1),(0,0)},{(2,0),(0,0)},{(2,1),(2,0),(0,0)},{(1,1),(0,0)},{(2,1),(1,1),(0,0)},{(2,0),(1,1),(0,0)},{(2,1),(2,0),(1,1),(0,0)},{(1,0),(0,0)},{(2,1),(1,0),(0,0)},{(2,0),(1,0),(0,0)},{(2,1),(2,0),(1,0),(0,0)},{(1,1),(1,0),(0,0)},{(2,1),(1,1),(1,0),(0,0)},{(2,0),(1,1),(1,0),(0,0)},{(2,1),(2,0),(1,1),(1,0),(0,0)},{(0,1),(0,0)},{(2,1),(0,1),(0,0)},{(2,0),(0,1),(0,0)},{(2,1),(2,0),(0,1),(0,0)},{(1,1),(0,1),(0,0)},{(2,1),(1,1),(0,1),(0,0)},{(2,0),(1,1),(0,1),(0,0)},{(2,1),(2,0),(1,1),(0,1),(0,0)},{(1,0),(0,1),(0,0)},{(2,1),(1,0),(0,1),(0,0)},{(2,0),(1,0),(0,1),(0,0)},{(2,1),(2,0),(1,0),(0,1),(0,0)},{(1,1),(1,0),(0,1),(0,0)},{(2,1),(1,1),(1,0),(0,1),(0,0)},{(2,0),(1,1),(1,0),(0,1),(0,0)},{(2,1),(2,0),(1,1),(1,0),(0,1),(0,0)}} ok

The number 0 also represent the empty set. The sets and the vectors are stored in a set parameter stack allocated at zst plus two help stacks at xst and yst. Sets can have sets, vectors and non negative numbers as members. Vectors can have sets, vectors and non negative numbers as components. Main set manipulation words:

set= \ -- flag | s --

member \ -- flag | x s --     If x is a positive number it first has to be pushed to the zst-stack manually with the word >zst

subset \ -- flag | s s' -- 

union \ -- | s s' -- s⋃s'

intersection \ -- | s s' -- s⋂s'

diff \ -- | s s' -- s\s'

powerset \ -- | s -- p(s) 

power# \ n -- | s -- {t∈p(s): |t|=n }

multiunion \ -- | {s1,s2,...,sn} -- s1⋃s2⋃...⋃sn

card \ -- |s| | s --   cardinality

@split \ ad --   ad=yst, zst   split the (non empty) top set/list into tail set and head object

@obj \ ad -- i   ad=xst, yst, zst  i=0 if top of stack is a number, 1 if vector and 2 if non empty set

In interpretation mode there also is a word |:

{ 1 100 | prime } cr zet.

{2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97} ok

{ 1 10000 | pairprime } card . 409  ok
