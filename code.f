: loc{ [compile] { ; immediate

\ Single cell computational arithmetic

: ?undef ( -- flag ) bl word find nip 0= ; 
\ flag is true if word undefined

: .s depth if >r recurse r> dup . then ;

?undef 0> [if] : 0> ( n -- flag )  0 > ; [then]

: ugcdl ( a b -- c )              \ Algorithm from Wikipedia
  0 loc{ a b t -- c }
  a b u< if a b to a to b then    \ a>=b as unsigned numbers
  begin b \ while b<>0
  while b to t \ t <- b
     a 0 b um/mod drop to b       \ b <- a(mod b)
     t to a \ a <- t
  repeat a ;

: ugcd ( a b -- c ) \ a version without local variables
  2dup u< if swap then   \ smallest of a b on top of stack (tos)
  ?dup 0= if exit then   \ return second value if tos is zero
  begin tuck             \ y x y first time b a b
     0 swap um/mod       \ y x 0 y --> y r q
     drop dup 0=         \ y r [r=0]
  until drop ;           \ y

?undef umod [if]
: umod ( u1 u2 -- u3 ) 0 swap um/mod drop ;
[then]

: u*mod ( u1 u2 u3 -- u4 )
  >r r@ umod swap r@ umod um*
  r> um/mod drop ;

cell 8 * constant bits

: log~ ( n -- nr ) \ nr = 1+²log n
  bits here !                \ bits is stored at the address 'here'
  bits 0                     \ do-loop from i=0,...,bits-1
  do 1 rshift ?dup 0=        \ shift tos at right test if zero
     if i 1+ here !          \ if zero store i+1 at 'here'
        leave                \ and leave the loop
     then 
  loop here @ ;

: u**mod loc{ b a m -- x }
  1                     \ preparation for repeated multiplication
  a log~ 0              \ n 0 n is the number of binary digits in a
  ?do a 1 i lshift and  \ flag the i-th digit of a is 0/1
     if b m u*mod       \ multiply if flag
     then b dup m       \ square b for each i: b b^2 b^4 b^8 ...
     u*mod to b         \ new squared number to b
  loop ;                \ result of the repeated multiplication

: invmod dup ( a m -- a' ) \ a m must be coprime
  dup 1 0 loc{ a m v c b }
  begin a
  while v a / >r
     c b s>d c s>d r@ 1 m*/ d- d>s to c to b  \ old c become new b
     a v s>d a s>d r> 1 m*/ d- d>s to a to v  \ old a become new v
  repeat b m mod dup to b 0<
  if m b + else b then ;

\ Pseudo prime number tests

variable rnd base @ hex 

: reset_seed 0ABCDEF1 rnd ! ; reset_seed 

: rand ( -- u )
  rnd @ 08088405 * 1+ dup rnd ! ;

: random ( u1 -- u2 ) 
  rand um* nip ;

base ! 

: fermat ( numb -- flag ) \ numb odd
  dup 2 - random 2 +
  over 1- rot u**mod 1 = ; 

: 2/mod \ n -- r q
  dup 1 and swap 1 rshift ;

: get-rs 0 loc{ numb r -- r s } \ numb odd
  numb 1-
  begin dup 2/mod swap 0=       \ n qout rest=0
  while nip r 1+ to r
  repeat 2drop 
  r numb 1- r rshift ;

: get-a ( numb -- a )
  2 - random 2 + ;
  
: rabin-miller1 ( numb -- flag )    \ numb odd
  dup dup get-rs rot get-a false loc{ numb r s a flag } 
  a s numb u**mod 1 = 
  if true exit
  then r 0 
  ?do a s i lshift numb u**mod numb 1- = 
     if true to flag leave then
  loop flag ;

create pnr 
2 c, 3 c, 5 c, 7 c, 11 c, 13 c, 17 c, 19 c, 23 c, 29 c, 31 c, 37 c,

: rabin-miller2 ( numb a -- flag )
  over get-rs false loc{ numb a r s flag }
  a s numb u**mod 1 = 
  if true exit
  then r 0 
  ?do a s i lshift numb u**mod numb 1- = 
     if true to flag leave then
  loop flag ;

cell 4 = 
[if]
: rmx ( numb -- n ) \ 32 bit integers
  dup 2047 u< if drop 1 exit then
  dup 1373653 u< if drop 2 exit then
  dup 25326001 u< if drop 3 exit then
    3215031751 u< if 4 else 5 then ;
[else]
: rmx \ numb -- n 64 bit integers
  dup 2047 u< if drop 1 exit then
  dup 1373653 u< if drop 2 exit then
  dup 25326001 u< if drop 3 exit then
  dup 3215031751 u< if drop 4 exit then
  dup 2152302898747 u< if drop 5 exit then
  dup 3474749660383 u< if drop 6 exit then
  dup 341550071728321 u< if drop 8 exit then
  3825123056546413051 u< if 11 else 12 then ;
[then]

: rabin-miller ( numb -- flag )
  dup rmx 0
  do dup i pnr + c@ rabin-miller2 0=
     if 0= leave then
  loop 0= 0= ;

: fermat-rabin-miller ( numb -- flag ) \ numb odd
  dup fermat
  if rabin-miller
  else 0=
  then ;

: nextprime ( numb -- prime )
  dup 3 u< if drop 2 exit then
  1 or
  begin dup fermat-rabin-miller 0=
  while 2 +
  repeat ;

: prime ( numb -- flag )
  dup 3 u< if 2 = exit then
  dup 1 and 0= if drop false exit then
  rabin-miller ;

\ Square root

: sqrtf \ m -- n
  0 d>f fsqrt f>s ;

: sqrtfslow \ m -- n Newton-Ralphson´s method
  dup 4 u< if dup if drop 1 then exit then
  dup 1- >r 1 rshift
  begin r@ over 0 swap um/mod nip
     over + 1 rshift tuck u> 0=
  until r> drop ;

: sqrtc \ m -- n
  1- sqrtf 1+ ;

\ Integer factoring

: func ( numb n -- m ) dup um* 1 0 d+ rot um/mod drop ; 

: pollard1 ( numb start -- pfac flag )
  dup dup loc{ numb start alpha beta } 0  \ numb is an odd composite 
  begin drop numb alpha func to alpha
     numb dup beta func func to beta
     alpha beta - abs                  \ |alpha-beta|
     numb ugcd dup numb =              \ gcd flag 
     if false exit 
     then dup 1 = 0=                   \ gcd<>1 
  until true ;

: pollard2 \ numb -- prime numb>1
  dup 1 and 0= if drop 2 exit then
  dup prime if exit then
  dup sqrtf dup * over = 
  if sqrtf exit then -1 2              \ numb 100 0 
  do dup i pollard1                    \ numb pfac flag
     if leave                          \ numb pfac
     then drop                         \ numb
  loop nip ;                           \ pfac

: pollard \ n -- p1 ... pk      
  dup pollard2 2dup =                  \ n q f=
  if drop exit                         \ n
  then dup >r 
  0 swap um/mod nip recurse            \ q n/q
  r> recurse ;

: pollard# \ numb -- p1 ... pk k
  depth >r
  pollard depth r> - 1+ ;

\ Sorting the stack

: lower \ m1 ... mn m n+1 -- m1 ... m ... mi n+1  
\ lower m on stack until next number not is greater
  dup 2 =
  if drop 2dup u>
     if swap
     then 2 exit
  then >r 2dup u> 0= 
  if r> exit
  then r> rot >r 
  1- recurse 1+ r> swap ;

: sort \ m1 ... mn n -- s1 ... sn n o(n²)
  dup 3 <
  if dup 2 =
     if drop 2dup u> 
        if swap 
        then 2 
     then exit
  then dup >r
  1- recurse roll 
  r> lower ;

\ Arithmetical functions

: radical1 ( n -- r )
  1 dup loc{ n radical prime }
  n pollard# sort 0 
  do dup prime = 0=
     if dup radical * to radical
     then to prime 
  loop radical ;
  
: undequ ( a b c -- a b c a=b )
  >r 2dup = r> swap ;

: radical2 ( n -- r )
  1 loc{ n prime }
  n pollard# sort 1 swap 0 
  do over prime =
     if nip
     else over to prime *
     then 
  loop ; 

: radical ( n -- r )
  1 swap
  pollard# sort
  1 swap 0
  do undequ if nip else * then
  loop nip ;

: totients1 ( n -- t )
  1 loc{ tot }
  pollard# sort 0
  do 2dup =
     if tot * to tot
     else 1- tot * to tot
     then
  loop tot ;

: totients ( n -- t )
  1 swap
  pollard# sort
  1 swap 0
  do undequ if * else swap 1- * then
  loop nip ;

: drops 0 ?do drop loop ;

: mobius ( n -- my )
  dup 2 u< if drop 1 exit then
  1 swap
  pollard# sort
  dup true loc{ facts sqrfree } 0
  do 2dup =
     if false to sqrfree
        facts i - drops leave 
     then drop
  loop sqrfree
  if facts 1 and
     if -1
     else 1
     then
  else 0
  then nip ;

: bigomega ( n -- b )
  dup 2 u< if drop 0 exit then
  pollard# dup >r drops r> ;

: smallomega ( n -- s )
  dup 2 u< if drop 0 exit then
  1 swap
  pollard# sort 0 swap 0
  do undequ 0= if 1+ then nip
  loop nip ;

: ** ( b e -- b^e )
  dup 0= if 2drop 1 exit then
  1 swap 0 do over * loop nip ;

: m** ( b e -- d )
  dup 0= if 2drop 1. exit then
  1 swap 1. rot 0
  do 2over m*/ loop 2nip ;

: -1** ( n -- i )
  1 and if -1 else 1 then ;

: unit* ( i j -- k )
  xor 1+ ;

: ufaculty ( u -- u! )
  dup 2 u< if drop 1 exit then
  dup 1- recurse * ;

: umfaculty ( u -- ud )
  dup 2 u< if drop 1. exit then
  dup 1- recurse rot 1 m*/ ;

: oddpart ( a -- i m )
  0 swap
  begin 2/mod swap 0=
  while 1 under+
  repeat 2* 1+ ;

: legendre ( a p -- i )
  tuck dup 1- 2/ swap u**mod dup 1 >
  if swap - else nip then ;

: jacobi ( a n -- j )
  1 loc{ a n unit }
  a n ugcd 1 = 0= if 0 exit then 
  begin n 1 = a 1 = or if unit exit then
     a n mod ?dup 0= if 0 exit then
     oddpart to a 1 and
     if n dup * 1- 3 rshift -1** unit unit* to unit 
     then a n ugcd 1 = 0= if 0 exit then
     n a to n to a
     a 1- n 1- * 2 rshift -1** unit unit* to unit
  again ; 

: kronecker ( a n -- j )
  0 loc{ a n unit }
  n 0= if a abs 1 = if 1 else 0 then exit then
  n dup abs to n 0<
  if a 0< if -1 else 1 then
  else 1
  then to unit
  a dup abs to a \ old_a
  n oddpart to n dup \ old_a i i
  if a 1 and 0= \ old_a i f
     if 2drop 0 exit 
     else 1 and \ old_a f
        if a 7 and 1+ 4 and \ old_a
           if unit negate to unit then \ old_a
        then
     then
  else drop
  then a n jacobi ?dup 0=
  if drop 0 exit then
  unit unit* to unit \ old_a
  0< if n 1- 2/ -1** else 1 then \ ±1
  unit unit* ;

\ Gaussian integers 
\ Typical restriction, the norm must be a single cell integer

: gnorm \ a b -- u 
  dup * swap dup * + ;

: g< \ a b c d -- flag
  gnorm -rot gnorm u> ;

\ print single cell signed numbers without spaces
\ http://www.forth.com/starting-forth/sf7/sf7.html
: .sign-w/o-space \ n --
  dup 0< swap abs 0 <# #s rot sign #> type ;

: g. \ a b --
  2dup 0. d= if d. exit then
  swap dup \ b a a
  if over 
     if dup .sign-w/o-space
     else dup .
     then
  then swap dup 0< 0= \ a b f
  if dup \ a b b
     if swap if ." +" then dup 1 > \ b f
        if .sign-w/o-space else drop then ." i" space
     else 2drop
     then
  else nip dup \ b b 
     if dup -1 < \ b f
        if .sign-w/o-space else ." -" drop then ." i" space
     else drop
     then
  then ;

: .gs depth 2 < if exit then 2>r recurse 2r> 2dup g. ;

: g+ \ a b c d -- a+c b+d
  under+ under+ ;

: g- \ a b c d -- a-c b-d
  negate under+ negate under+ ;

: g* loc{ a b c d -- e f } 
  a c m* b d m* d- d>s a d m* b c m* d+ d>s ;

: g/ loc{ a b c d -- e f }
  c dup m* d dup m* d+ d>f
  a c m* b d m* d+ d>f fover f/
  b c m* a d m* d- d>f frot f/
  fswap f>d d>s f>d d>s ;

: g/' loc{ a b c d -- e f }
  c dup m* d dup m* d+ d>f
  a c m* b d m* d+ d>f fover f/ fround
  b c m* a d m* d- d>f frot f/ fround
  fswap f>d d>s f>d d>s ;

: gmod ( a b c d -- e f )
  2over 2over g/' g* g- ;

: ggcd ( a b c d -- e f ) \ Euclid's algorithm
  0 0 loc{ a b c d s t }
  a b c d g<
  if a c to a to c
     b d to b to d
  then
  begin c d or \ while c+id<>0
  while c to s d to t
     a b c d gmod to d to c
     t to b s to a
  repeat a b ;

: gnormal ( a b -- c d ) \ c>=d and c>=0
  2dup abs swap abs >
  if 0 1 g* then over 0< 
  if negate swap negate swap then ;

\ http://mathworld.wolfram.com/GaussianPrime.html
: gprime1 \ n --flag
  abs dup prime swap 3 and 3 = and ;

: gprime \ a b -- flag 
  over 0= if nip gprime1 exit then
  dup 0= if drop gprime1 exit then
  gnorm prime ;

: .normgp ( a b norm -- )
  cr 8 .r space g. ;

: .gprime loc{ norm -- }
  norm 2 = if 1 1 norm .normgp exit then
  norm sqrtf 1+ 0
  do i 0
     ?do i j gnorm norm =
        if i j gprime 
           if j i norm .normgp then
        then
     loop
  loop ; 

: .gps 1+ 2 do i .gprime loop ;

: gfunc ( a b x y -- u v )
  2dup g* -1 0 g+ 2swap gmod ;

: gpollard1 ( a b c d -- p q flag ) \ a+ib not having factor 2
  2dup loc{ a b alpha1 alpha2 beta1 beta2 } 0.
  begin 2drop a b alpha1 alpha2 gfunc to alpha2 to alpha1
     a b 2dup beta1 beta2 gfunc gfunc to beta2 to beta1
     alpha1 alpha2 beta1 beta2 g-
     a b ggcd 2dup a b d=
     if false exit
     then 2dup gnorm 1 = 0=
  until true ;

: gpollard2 ( a b -- p q )
  false loc{ flag }
  2dup gnorm 1 = if exit then
  2dup 2 0 gmod d0= if 2drop 1 1 exit then
  2dup gprime if exit then -1 1
  do i 0
     do 2dup j i gpollard1
        if true to flag leave then 2drop
     loop flag if leave then
  loop 2swap 2drop ;

: gfac ( a b -- p1 q1 ... pk qk )
  2dup gpollard2 2over 2over gnorm -rot gnorm =
  if 2drop exit
  then 2dup 2>r g/ recurse 2r> recurse ;

\ Prime functions

: prevprime ( numb -- prime )
  dup 3 u< if drop 2 exit then
  1- 1 or 
  begin dup fermat-rabin-miller 0=
  while 2 -
  repeat ;

?undef under+ 
[if]
: under+ ( a b c -- a+c b ) rot + swap ; 
[then]

: 8/mod ( n -- r q ) dup 7 and swap 3 rshift ;
: 256/mod ( n -- r q ) dup 255 and swap 8 rshift ;
: 65536/mod ( n -- r q ) dup 65535 and swap 16 rshift ;

\ bit arrays

: adbit ( i ad -- j a ) swap 8/mod rot + ;

: setbit \ i ad --
  adbit 1 rot lshift over c@ or swap c! ;

: tglbit \ i ad --
  adbit 1 rot lshift over c@ xor swap c! ;

: clrbit \ i ad --
  adbit 1 rot lshift 255 xor over c@ and swap c! ;

: bit@ \ i ad -- bit
  adbit c@ swap rshift 1 and ;

: bit! \ bit i ad --
  rot if setbit else clrbit then ;

: bit? ( i ad -- f ) bit@ negate ;

: bitarray \ bits -- ad | n -- bit
  8/mod swap 0= 0= negate + allocate throw
  create dup ,
  does> @ swap 8/mod rot + bit@ ;

\ multiple byte read/write in arrays

variable ebuf
1 ebuf ! ebuf c@ negate
[if] \ little-endian
: mb! ( n ad i -- ) 2>r ebuf ! ebuf 2r> cmove ;
: mb@ ( ad i -- n ) ebuf 0 over ! swap cmove ebuf @ ;
[else] \ big-endian
: mb! ( n ad i -- ) 2>r ebuf ! ebuf cell + r@ - 2r> cmove ;
: mb@ ( ad i -- n ) ebuf 0 over ! cell + over - swap cmove ebuf @ ;
[then]

\ the sieve of Eratosthenes 
0xfffff constant plim
82025 constant pi_plim
\ 16777215 constant plim      
\ 1077871 constant pi_plim    
\ 100000000 constant plim \ 100000000 takes 6 times 
\ 5761455 constant pi_plim \ longer time to load

plim bitarray prime_ constant pbuf
\ prime_ ( n -- flag ) n<plim

: resetsieve ( -- )
  pbuf plim 8/mod swap 0= 0= - + pbuf 
  do true i ! cell +loop ;

: sieve ( -- )
  resetsieve
  0 pbuf clrbit 
  1 pbuf clrbit
  plim sqrtf 1+ 2
  do i pbuf bit@
     if plim 1+ i dup *
        do i pbuf clrbit j +loop
     then 
  loop ; sieve 

plim prevprime constant pmax_

: nextprime_ ( numb -- prime ) \ numb<pmax_
  dup 3 u< if drop 2 exit then
  1 or
  begin dup prime_ 0=
  while 2 +
  repeat ;

: prevprime_ ( numb -- prime )
  dup 3 u< if drop 2 exit then
  1- 1 or 
  begin dup prime_ 0=
  while 2 -
  repeat ;

: prime ( n -- flag ) dup plim u> if prime else prime_ negate then ;
: nextprime ( numb -- prime ) dup pmax_ u< if nextprime_ else nextprime then ;
: prevprime ( numb -- prime ) dup plim u< if prevprime_ else prevprime then ;

plim 65536/mod swap 0= 0= - constant breaknumbers
pi_plim 2* allocate throw constant pnrbuf 
breaknumbers cells allocate throw constant breaks 

: init_pnr ( -- )
  0 pad ! 0 breaks ! 
  1 pi_plim 1+ 1 
  do nextprime_ dup \ p p
     65536/mod pad @ = 0= \ p r flag
     if 1 pad +! \ p r
        i 1- pad @ cells breaks + ! \ p r
     then pnrbuf i 1- 2* + 2 mb! 1+ \ p+1
  loop drop ; init_pnr 
\ it takes less than a second to store all primes less than 2^24

: newintbreaks ( i j x -- i' j' ) 
  >r 2dup + 2/ dup
  cells breaks + @ r> u> \ i j k flag 
  if -rot nip else nip then ; 

: pnr@ ( n -- p ) \ n<1077871 
  1- dup >r 2* pnrbuf + 2 mb@ 
  breaknumbers 0 
  begin r@ newintbreaks 2dup - 2 u< 
  until rdrop nip 16 lshift + ; 

: newintpnr ( i j x -- i' j' ) 
  >r 2dup + 2/ dup pnr@ r> u> \ i j k flag 
  if -rot nip else nip then ; 

: fpi pi ;

: pi ( x -- n ) >r pi_plim 1+ 0  \ x<16777215
  begin r@ newintpnr 2dup - 2 u< \ i j flag 
  until rdrop nip ;

\ NESTED SETS WITH CARTESIAN PRODUCTS

\ Stacks_____

: cs negate 2/ ;
: listflag 1 and ;

: objsize \ bc -- n 
  dup 0< if cs 1+ else drop 1 then ;

cell negate constant -cell

: >stack ( n ad -- )  cell over +! @ ! ;
: stack> ( ad -- n )  dup @ @ -cell rot +! ;
: >stack> ( n ad -- m )  dup @ @ -rot @ ! ;
: stack@ ( ad -- n )  @ @ ;
: stack! ( n ad -- )  @ ! ;
: stack+! ( n ad -- )  @ +! ;

1 22 lshift cells allocate throw dup constant xst dup ! 

: >xst ( n -- )  xst >stack ;
: xst> ( -- n )  xst stack> ;
: >xst> ( n -- m )  xst >stack> ;
: xst@ ( -- n )  xst @ @ ;
: xst! ( n -- )  xst @ ! ;
: xst+! ( n -- )  xst @ +! ;

: >>xst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >xst loop r> >xst ;
: xst>> ( -- x1 ... xn bc )  xst@ >r xst> cs 0 ?do xst> loop r> ;

1 22 lshift cells allocate throw dup constant yst dup ! 

: >yst ( n -- )  yst >stack ;
: yst> ( -- n )  yst stack> ;
: >yst> ( n -- m )  yst >stack> ;
: yst@ ( -- n )  yst @ @ ;
: yst! ( n -- )  yst @ ! ;
: yst+! ( n -- )  yst @ +! ;

: >>yst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >yst loop r> >yst ;
: yst>> ( -- x1 ... xn bc )  yst@ >r yst> cs 0 ?do yst> loop r> ; 

cell 1- log~ constant cellshift

: stack-depth ( ad -- n )  dup @ swap - cellshift rshift ;
: stack-cl ( ad -- )  dup ! ;
: stack-empty ( ad -- flag )  dup @ = ;

1 22 lshift cells allocate throw dup constant zst dup ! 

: >zst ( n -- )  zst >stack ;
: zst> ( -- n )  zst stack> ;
: >zst> ( n -- m )  zst >stack> ;
: zst@ ( -- n )  zst @ @ ;
: zst! ( n -- )  zst @ ! ;
: zst+! ( n -- )  zst @ +! ;

: >>zst ( xn ... x1 bc -- )  >r r@ cs 0 ?do >zst loop r> >zst ;
: zst>> ( -- x1 ... xn -n )  zst@ >r zst> cs 0 ?do zst> loop r> ;

: showx xst stack-depth if xst> >r recurse r> dup . >xst then ;
: showy yst stack-depth if yst> >r recurse r> dup . >yst then ;
: showz zst stack-depth if zst> >r recurse r> dup . >zst then ;

: >zet ( s -- | -- s)
  >>yst yst> dup >xst cs 0 ?do yst> >zst loop xst> >zst ; 

: zet> ( -- s | s -- )
  zst> dup >yst cs 0 ?do zst> >xst loop yst> >xst xst>> ; 

\ Set manipulations_____

\ bundle code bc=-(2n+1)
\ z1...zn bc

: setdrop \ ad -- 
  dup @ @ cs cells cell+ negate swap +! ;

: setdup \ ad -- 
  >r
  r@ @ @ cs cells                 \ n'
  r@ @ over -                     \ n' ad1
  r@ @ cell+                      \ n' ad1 ad2
  rot cell+ dup r> +! cmove ;

: setover \ ad --
  dup >r @ @ cs cells cell+       \ nr of bytes 1'st set 
  r@ @ swap -                     \ ad to 2'nd set
  dup @ cs cells cell+ dup >r -   \ ad to 3'rd set
  cell+ r> r@ @ cell+             \ ad to move to
  swap dup r> +! cmove ;

: setcopy loc{ ad1 ad2 -- }
  ad1 @ @ cs cells             \ n'
  ad1 @ over - swap cell+      \ ad1-n' n
  ad2 @ cell+ over ad2 +! swap cmove ;

: setmove \ ad1 ad2 --
  swap dup rot setcopy setdrop ;

: adn1 zst@ cs cells zst @ over - swap cell+ ;
: adn2 adn1 drop cell - dup @ cs cells tuck - swap cell+ ;
: adn3 adn2 drop cell - dup @ cs cells tuck - swap cell+ ;

: zdup  zst setdup ;
: zdrop  zst setdrop ;
: zover  adn2 tuck zst @ cell+ swap cmove zst +! ;
: zswap  zover adn2 adn3 rot + move zdrop ;
: znip  zswap zdrop ;
: ztuck  zswap zover ;
: zrot  zst>> zswap >>zst zswap ; 

\ Output of sets_____

0 value addr1

: addr1- \ -- 
  addr1 1- to addr1 ;

: fillad$ \ addr n -- 
  dup 1- negate addr1 + dup to addr1 swap move addr1- ;

: n>addr1 \ n -- 
  0 <# #s #> fillad$ ;

: a>addr1 \ c -- 
  addr1 c! addr1- ;

: cardinality \ -- n | s --
  zst> cs dup >xst 0
  ?do zst@ 0<
     if zst@ dup cs negate xst+! >r zdrop r> cs 1+
     else zst> drop 1
     then
  +loop xst> ;

: foreach \ -- n 0 | s -- z1...zn
  zdup cardinality zst> drop 0 ;

: closep \ -- bc asc
  zst@ dup listflag if [char] ) else [char] } then ;

: openp \ bc -- asc
  listflag if [char] ( else [char] { then ;

: list$ \ ad -- ad n | s -- 
  dup to addr1 false loc{ addr2 flag }
  closep a>addr1
  foreach 
  do flag if [char] , a>addr1 then zst@ 0<
     if addr1 recurse 2drop
     else zst> n>addr1
     then flag 0= if true to flag then
  loop openp a>addr1
  addr1 1+ addr2 over - 1+ ; 

1 20 lshift dup allocate throw swap cell - + constant printbuf

: zet. \ -- | s -- 
  zst@ 0=
  if zst> .
  else printbuf list$ type
  then ; 

: set. \ yst,xst -- 
  zst setcopy zet. ;

\ Analyzing sets_____

: ?obj \ x -- 0,1,2
  dup 0<
  if listflag
     if 1 else 2 then
  else drop 0
  then ;

: _split \ ad --   ad=yst,zst 
  dup >r @ cell - @ 0< 0=
  if r@ stack> 2 + r@ stack> swap r@ >stack r> >stack exit then
  r@ stack>
  r@ xst setmove
  xst@ cs 1+ 2* + r@ >stack
  xst r> setmove ;

: ysplit \ -- | s -- s' x  in yst stack
  yst _split ;

: zsplit \ -- | s -- s' x
  zst _split ;

\ Set equal, subset and membership_____

: zetmerge \ -- | s s' -- s" 
  zst yst setmove
  yst@ zst> + 
  yst zst setmove
  zst! ;
  
: ymerge yst xst setmove xst@ yst> + xst yst setmove yst! ;
: zmerge zetmerge ;

: vmerge \ -- | v v'-- v" 
  zst yst setmove
  yst@ zst> + 1+
  yst zst setmove
  zst! ;

: _fence \ ad -- | x -- {x} 
  dup >r stack@ ?obj 
  case 0 of -2 r@ >stack endof 
       1 of r@ stack@ 1- r@ >stack endof
       2 of r@ stack@ 2 - r@ >stack endof
  endcase rdrop ;

: xfence xst _fence ;
: yfence yst _fence ;
: zfence zst _fence ;
  
: first-sort \ -- | s -- n1...nk -2k
  0 loc{ counter } 0 >xst 0 >yst
  foreach
  ?do zst@ ?obj
     case 0 of counter 1+ to counter zst> endof
          1 of zfence xst zst setmove zetmerge zst xst setmove endof
          2 of zfence yst zst setmove zetmerge zst yst setmove endof
     endcase
  loop counter sort 2* negate >zet ;

: next-element-ad \ ad1 -- ad2
  dup @ objsize cells - ;

: set-sort \ ad --
  loc{ ad }
  first-sort
  xst zst setmove zetmerge
  yst zst setmove zetmerge ;

: smember \ n -- flag | s -- 
  zst@ cs false loc{ m flag } 
  foreach 
  ?do zst@ 0< 
     if m zst@ cs 1+ - to m zdrop 
     else m 1- to m dup zst> 2dup > 
        if false to flag 2drop 
           m cells negate zst +! leave 
        then = 
        if true to flag 
           m cells negate zst +! leave 
        then 
     then 
  loop drop flag ; 

: vect= \ s -- flag | s' --
\ s non empty list not including non empty sets
  dup zst@ = 0=
  if zdrop cs 0 ?do drop loop false exit
  then true loc{ flag } zst> drop cs 0
  ?do flag
     if zst> = 0= if false to flag then
     else zst> 2drop 
     then
  loop flag ;

: vector= \ -- flag | s s' --
  zet> vect= ;

: vmember \ -- flag | s s' --
  zswap zst yst setmove
  zst@ cs false loc{ m flag }
  foreach
  ?do zst@ ?obj 
    case 0 of m 1 - to m zst> drop endof
         1 of m zst@ cs 1+ - to m 
              yst zst setcopy vector=
              if true to flag
                 m cells negate zst +! leave
              then endof
         2 of m zst@ cs 1+ - to m 
              zst@ cs 1+ cells negate zst +! endof
    endcase
  loop yst setdrop flag ;

: secobjad \ -- ad | x y -- x y
  zst @ zst@ 0< if zst@ cs 1+ cells - else cell - then ;

: routout \ -- x | x s -- s
  secobjad dup @ swap dup cell+ swap zst@ cs 1+ cells move zst> drop ;

0 value 'subset  
: subset \ -- flag | s s' --
  'subset execute ;

: zet= \ -- flag | s s' --
  zover zover subset
  if zswap subset
  else zdrop zdrop false
  then ; 

: zet-member \ -- flag | s s' -- 
  zswap zst yst setmove
  begin zst@                         \ set not empty?
  while zsplit zst@ ?obj 2 =      \ element is a set?
     if yst zst setcopy zet=  
        if yst setdrop zdrop true exit then
     else zst@ ?obj if zdrop else zst> drop then
     then 
  repeat yst setdrop zdrop false ;

: member \ -- flag | x s --
  secobjad @ ?obj
  case 0 of routout smember endof
       1 of vmember endof
       2 of zet-member endof
  endcase ;

:noname \ -- flag | s s' --          \ the subset code
  zst @ cell - 2@ or 0=
  if zdrop zdrop true exit then      \ true if both sets are empty
  zswap zst yst setmove
  begin yst@                         \ set is not empty?
  while ysplit yst@ ?obj
     if yst zst setmove zover member
     else yst> zdup smember 
     then 0= if yst setdrop zdrop false exit then
  repeat yst> drop zdrop true ; to 'subset

\ Set algebra_____

: reduce \ -- | s -- s' 
  0 >yst foreach
  ?do zfence zdup zst> drop
     yst zst setcopy member
     if zdrop
     else yst zst setmove
        zetmerge zst yst setmove
     then
  loop yst zst setmove ;

: union \ -- | s s' -- s"
  zetmerge zst set-sort reduce ;

: intersection \ -- | s s' -- s" 
  0 >xst zst yst setmove
  begin zst@
  while zsplit zfence zdup zst> drop
     yst zst setcopy member
     if xst zst setmove zetmerge zst xst setmove
     else zdrop
     then 
  repeat zdrop yst setdrop
  xst zst setmove reduce ; 

: diff \ s s' -- s" 
  0 >xst zst yst setmove 
  begin zst@
  while zsplit zfence zdup zst> drop
     yst zst setcopy member
     if zdrop 
     else xst zst setmove zetmerge zst xst setmove
     then
  repeat zdrop yst setdrop
  xst zst setmove reduce ;

: multincl \ s x -- s'
  0 >xst zfence zst yst setmove
  begin zst@
  while zsplit yst zst setcopy union zfence
     xst zst setmove zetmerge zst xst setmove
  repeat zdrop yst setdrop xst zst setmove ;

: powerset \ s -- s'
  zst@ 0= if -2 >zst exit then
  zsplit zfence zst yst setmove recurse
  zdup yst zst setmove zst> drop multincl
  zetmerge ;

: cartprod \ s s' -- s"
  zst yst setmove
  zst xst setcopy xst> drop cardinality 0 0 >zst
  ?do xfence -1 xst+! 
     yst setdup
     begin yst@
     while ysplit yfence -1 yst+!
        xst zst setcopy
        yst zst setmove vmerge
        zfence
        zetmerge
     repeat yst> drop xst setdrop 
  loop yst setdrop ;

\ {x1,...,xn} -- {{x1},...,{xn}}
: infence \ -- | s -- s' 
  0 >xst foreach 
  ?do zfence zfence
     xst zst setmove zetmerge
     zst xst setmove 
  loop xst zst setmove ; 

\ p(A,k)=p(A\{f(A)},k)+(p(A\{f(A)},k-1)%f(A))
: power# \ n -- | s -- s' 
  ?dup 0= if zdrop 0 >zst zfence exit then 
  dup 1 = if drop infence exit then 
  dup zdup cardinality = 
  if drop zfence exit then 
  dup 1 = if drop infence exit then 
  zsplit zfence zst xst setmove 
  dup zdup recurse 
  zswap 1- recurse xst zst setmove 
  zst> drop multincl 
  zetmerge ; 

\ from rosetta code
: choose \ n k -- nCk 
  1 swap 0
  ?do over i - i 1+ */
  loop nip ;

\ {s1,...,sn} -- s1U...Usn
: multiunion \ -- | s -- s'
  foreach 0 >zst
  ?do zetmerge
  loop zst set-sort reduce ;

\ {s1,...,sn} s' -- {s1Us',...,snUs'}
: zetcup \ -- | s s' -- s"
  zst xst setmove 0 >yst foreach
  ?do xst zst setcopy union zfence
     yst zst setmove zetmerge zst yst setmove
  loop xst setdrop yst zst setmove ;

\ {s1,...,sn} s' -- {s1&s',...,sn&s'}
: zetcap \ -- | s s' -- s"
  zst xst setmove 0 >yst foreach
  ?do xst zst setcopy intersection zfence
     yst zst setmove zetmerge zst yst setmove
  loop xst setdrop yst zst setmove ;

\ { s1,...,sn} {t1,...,tm} -- {siUtj}ij
: zetunion \ -- | s s' -- s"
  0 >xst zst yst setmove foreach
  ?do yst zst setcopy
     zswap zetcup
     xst zst setmove union
     zst xst setmove
  loop yst setdrop xst zst setmove ; 

: functions \ -- | s s' -- s"
  secobjad @ 0= if zdrop -2 >zst exit then
  secobjad @ -2 = if cartprod infence exit then
  zswap zsplit zfence zst xst setmove
  zover recurse zswap xst zst setmove
  zswap cartprod infence zetunion ;

\ Input of sets_____

0 create match ,
true value sort?

: { \ --
  1 match +! depth >xst true to sort? ;

: } \ x1...xk -- 
  depth xst> - 2* negate
  -1 match +! >zet sort?
  if zst set-sort then reduce match @
  if zet> then true to sort? ; 

: q  xst stack-cl yst stack-cl zst stack-cl 0 match ! abort ;

: (  { ;

: ) \ x1...xk --
  depth xst> - 2* 1+ negate 
  -1 match +! >zet match @ if zet> then ; 

\ cond ( n -- flag )
: all dup = ;
: odd 1 and ; 
: 1mod4 4 mod 1 = ; 
: 3mod4 4 mod 3 = ; 
: sqr dup sqrtf dup * = ;
: sqrfree dup radical = ;
: pairprime dup prime over 2 + prime rot 2 - prime or and ;  
: notpairprime dup prime swap pairprime 0= and ;
: semiprime bigomega 2 = ;
: uniprime smallomega 1 = ;
: biprime smallomega 2 = ;

: 2sqrsum dup 0 
  ?do dup i dup * - dup
     0< if drop false leave then 
     sqr if true leave then
  loop nip ;

\ 30 70 | odd
: | \ m n -- x1...xk 
  swap ' loc{ xt }
  ?do i xt execute if i then loop false to sort? ;

\ relations (A,B,R), R subset of AxB

: unfence zst> drop ;
: yzcopy1 yst zst setcopy ;
: yzcopy2 yst setover yst zst setmove ;

: domain \ (A,B,R) -- A
  unfence zdrop zdrop ;

: codomain \ (A,B,R) -- B
  unfence zdrop znip ;

: rel \ (A,B,R) -- R
  unfence znip znip ;

: image \ R -- s
  { foreach ?do unfence zst> zst> drop loop } ;

: coimage \ R -- s
  { foreach ?do unfence zst> drop zst> loop } ;

: subimage \ R s -- s'
  zst yst setmove
  { foreach 
  ?do unfence zst> zst> yst zst setcopy smember 0=
     if drop then
  loop } yst setdrop ;

: subcoimage \ R s -- s'
  zst yst setmove
  { foreach 
  ?do unfence zst> zst> yst zst setcopy swap smember 0=
     if drop then
  loop } yst setdrop ;

: func? \ -- flag | (A,B,R) --
  unfence znip 
  zst yst setmove true 
  begin zst@ 
  while zsplit zst> yst zst setcopy >zst zfence 
     subimage cardinality 1 = 0=
     if 0= zdrop yst setdrop exit then
  repeat zdrop yst setdrop ;

: eval \ x -- y | f --
  >zst zfence subimage unfence zst> ;

: pair \ s1 s2 -- (s1,s2)
  zswap zst@ 2 - zswap zst@ 2 - + 1- >zst ;

: triplet \ s1 s2 s3 -- (s1,s2,s3)
  zrot zst@ 2 - zrot zst@ 2 - zrot zst@ 2 - + + 1- >zst ;

: composition \ (A,B,R) (B,C,S) -- (A,C,SR) 
  0 >xst
  unfence zrot zdrop zrot unfence       \ C S A B R 
  zst yst setmove zdrop zswap           \ C A S
  zst yst setmove                       \ R S in yst 
  zswap zover zover cartprod            \ A C A×C 
  begin zst@ 
  while zsplit infence
     yzcopy1 zover zsplit znip subcoimage
     zst xst setmove
     yzcopy2 zover zsplit zdrop unfence subimage 
     xst zst setmove intersection zst@ zdrop 
     if unfence unfence zst> unfence >zst -5 >zst zfence
        xst zst setmove zetmerge zst xst setmove
     else zdrop
     then 
  repeat zdrop yst setdrop yst setdrop
  xst zst setmove triplet ;

: path? \ x y -- flag | E --
  swap >zst zfence 
  begin zover zover ztuck subimage      \ E s s s'
     union zdup dup smember             \ E s s" f
     if drop zdrop zdrop zdrop true exit then
     zswap zover zet=                   \ E s" s=s"
     if drop zdrop zdrop false exit then
  again ;

: ipair \ m n -- | -- (m,n)
  2>r ( 2r> ) ;

: loopset \ V -- s
  { foreach ?do ( zst> dup ) loop } ;

: rand-pair \ |V| -- | -- s
  dup random 1+ swap random 1+ ipair ; 

: rand-digraph \ |V| |E| -- | -- (V,E)
  { over 1+ 1 ?do i loop } 
  0 >zst 
  begin over rand-pair zfence union zdup cardinality over = 
  until 2drop 
  pair ; 

: rand-noloop-digraph \ |V| |E| -- | -- (V,E)
  { over 1+ 1 ?do i loop } 
  0 >zst 
  begin over rand-pair zfence union 
     zover loopset diff 
     zdup cardinality over = 
  until 2drop pair ; 

: sourceset \ (V,E) -- s 
  unfence image diff ; 

: sinkset \ (V,E) -- s 
  unfence coimage diff ; 

: xzmerge \ s -- 
  xst zst setmove
  zswap zetmerge 
  zst xst setmove ; 
  
: xzmergered
  xst zst setmove
  zswap zetmerge reduce
  zst xst setmove ; 
  
: toposort \ (V,E) -- s
  0 >xst                           \ empty set in x
  zdup sourceset zst yst setmove   \ source nodes in y
  unfence znip                     \ drop V keep E
  begin yst@                       \ while source nodes left
  while ysplit yst> dup            \ remove node m
     zdup >zst zfence zdup xzmerge \ add m to the set in x
     subimage                      \ set of all n: m→n
     begin zst@                    \ while that set non empty
     while zsplit zst> zswap       \ remove node n, E tos
        2dup ipair zfence diff     \ E:=E\{(m,n)}
        dup zdup >zst zfence       \ build set of all nodes..
        subcoimage zst@ 0=         \ ..pointing at n
        if >yst yfence ymerge      \ add n to y-set if empty
        else drop                  \ else drop n
        then zdrop zswap           \ drop set, swap E back
     repeat zdrop drop             \ drop empty set and node m
  repeat yst> drop zst@ zdrop      \ drop empty set and E
  if xst setdrop 0 >zst            \ if |E|>0 flag with empty set
  else xst zst setmove             \ else move the x-set to zst
     zst> 1- >zst                  \ mark it as ordered list
  then ; 

: dag? \ -- f | (V,E) -- 
  toposort zst@ 0= 0= zdrop ;

: rand-acyclic-digraph \ m n -- | -- (V,E)
  begin 2dup rand-noloop-digraph zdup dag? 0= 0=
  while zdrop
  repeat 2drop ;

\ Permutation groups

\ The number of permutations in a set
: ord \ -- n | s -- s
  zst> zst> 2dup >zst >zst
  cs 1+ swap cs swap / ;

\ The number of elements to be permuted in v
: numb \ -- n | v --
  zst@ cs zdrop ;

\ j=v(i)
: pmaps \ i -- j | v --
  zdrop cells zst @ + @ ;

\ composition of permutations as functions
: permcomp \ v1 v2 -- v1v2
  ( zst@ cs 1+ 1
  do zover zover i pmaps pmaps
  loop ) znip znip ; 

\ generation of cyclic permutation group
: pgen \ v -- s
  zst yst setcopy -1 1
  do zdup yzcopy1 permcomp zdup yzcopy1 vector=
     if numb 1+ i * 2* negate >zst leave then
  loop yst setdrop ; 

\ right coset
: prcoset \ s v -- s' 
  0 >xst
  zst yst setmove
  foreach
  ?do yzcopy1 permcomp zfence xzmerge
  loop yst setdrop xst zst setmove ;

\ left coset
: plcoset \ v s -- s'
  0 >xst
  zswap zst yst setmove
  foreach
  ?do yzcopy1 zswap permcomp zfence xzmerge
  loop yst setdrop xst zst setmove ;

\ componentwise composition of permutation sets
: permset* \ -- | s1 s2 -- s3
  0 >xst 
  zst yst setmove 
  foreach 
  ?do yzcopy1 plcoset 
  xzmergered
  loop yst setdrop 
  xst zst setmove ;

: permgroup? \ -- flag | s -- 
  zdup zdup permset* zet= ; 

\ Generation of standard permutations
: pidentity \ n -- | -- v
  >r ( r> 1+ 1 ?do i loop ) ;
  
: pcirc \ n -- | -- v
  >r ( r> dup 1 ?do i loop )  ;

: proll \ n -- | -- v
  >r ( r@ 1- dup 1 do i loop r> ) ; 

\ The number of element to be permuted in permutations in s
: perm# \ -- n | s -- s
  zst> zst> tuck >zst >zst cs ; 

\ Calculate the inverse permutation
: pinv \ v -- v'
  zdup adn2 drop adn1 -rot loc{ a2 a1 } cell/ 1
  do i dup 1- cells a2 + @ 1- cells a1 + ! loop znip ;

\ add the inverses to all permutations in s
: adinv \ s -- s'
  0 >xst zdup xzmerge foreach 
  do pinv zfence xzmerge 
  loop xst zst setmove reduce ;

\ generstes the group s' from the generators in s
: generate \ s -- s'
  zst yst setcopy 0 >xst foreach
  ?do pgen xzmerge 
  loop xst zst setmove reduce 1
  begin yzcopy1 zswap permset* 
     yzcopy1 permset* ord tuck =
  until yst setdrop drop ;

\ generate set of groups s' from set of generators s
: multigen \ s -- s'
  0 >xst foreach 
  ?do generate zfence xzmerge
  loop xst zst setmove reduce ;

\ Set of all subgroups to s
: psubgroups \ s -- s'
  perm# pidentity zfence zfence
  zst yst setmove foreach
  do yst zst setmove zdup zrot multincl 
     multigen union zst yst setmove
  loop yst zst setmove ;

?undef sp0 [if]
s0 constant sp0
r0 constant rp0
[then]

: new-data-stack \ u -- 
  dup aligned allocate throw + dup sp0 ! sp! ; 

100000 cells new-data-stack
100001 cells allocate throw 100000 cells + align rp0 ! q
