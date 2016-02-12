# ZET
NESTED SETS WITH CARTESIAN PRODUCTS AND A LOT OF ARITHMETICAL FUNCTIONS

The sets are implemented in three stacks located at 'xst', 'yst' and 'zst' as bundles on the stacks:

{ 1 2 3 ( 4 4 ) 3 { 5 6 } } cr showz cr zet.

1 2 4 4 -5 3 5 6 -4 -18

{1,2,(4,4),3,{5,6}} ok

The negative integers signals for vectors (odd) or sets (even). The absolut of the signals divided by 2 gives the number of preceding integers on the stack that are included in the bundle. The parameter stack for sets is 'zst' and all words beginning with z acts on that stack. The other stacks can be manipulated by words with the prefix set, for example: 'xst setdup',  'zst yst setcopy' and yst 'set.'.
