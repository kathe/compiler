        NEEDS -miscutil
        NEEDS -assemble

VARIABLE debug?    debug?   OFF
VARIABLE compile?  compile? OFF

0 VALUE #lcount
0 VALUE Look
0 VALUE token

CREATE token$  0 C, #256 CHARS ALLOT
CREATE prog$   0 C, #256 CHARS ALLOT

: char+!     ( c addr -- ) DUP >R COUNT + C!  1 R> C+! ;
: char-place ( c addr -- ) 1 OVER C!  CHAR+ C! ;

:   token>   ( -- c-addr u ) token$ COUNT ;
:  =token    ( char -- tf )  token =  ;
: <>token    ( char -- tf )  token <> ;
: getchar    ( -- ) EKEY TO Look Look ^M = 1 AND +TO #lcount ;
: init.input ( -- ) CR getchar ;

CREATE TAB$ 1 C, ^I C,
DEFER .OUT ( c-addr u -- )

: init.output ( -- ) compile? @ IF  ['] EVALUATE  ELSE  ['] TYPE  ENDIF  [IS] .OUT ;

        init.output

: cemits   ( c-addr u -- ) .OUT ;
: emits    ( c-addr u -- ) TAB$ COUNT .OUT    .OUT ;
: emitln   ( c-addr u -- ) CR$  COUNT .OUT   emits ;
: emitdln  ( c-addr u -- ) CR$  COUNT .OUT    .OUT ;
: emit2ln  ( c-addr u -- ) emitdln CR$  COUNT .OUT ;
: emit2lns ( c-addr u -- ) emit2ln TAB$ COUNT .OUT ;

: errors ( c-addr u -- ) 
        CR Bell ." Error on line " #lcount 0DEC.R ." , "
        TYPE ." , seen `" token> TYPE &' EMIT ;   

: init.error ( -- )          CLEAR #lcount ;
: aborts     ( c-addr u -- ) errors ABORT ;
: expected   ( c-addr u -- ) S"  expected" $+ aborts ;

: $aborts    ( $1 $2 -- )  &' CHAR-APPEND S"  `" 2SWAP $+ $+ aborts ;

: .undefined ( c-addr u -- ) S" Undefined identifier" 2SWAP $aborts ;
: .duplicate ( c-addr u -- ) S" Duplicate identifier" 2SWAP $aborts ;

0 VALUE lbase   -- local parameter counter
#100 =: maxentry

: $, ( c-addr u size -- ) 
        >S S MIN >R  
        R@ C, R@ 0 ?DO  C@+ C,  LOOP DROP 
        S> R> - CHARS ALLOT ; 

: SYMTAB ( size -- ) 
        CREATE  DUP 0< IF  0 , ABS DUP , 
                           1+ maxentry * ALLOT   
                     ELSE  HERE >R
                           0 ,  ( #items )
                           DUP >S ,  ( itemsize )
                           BEGIN  BL <WORD> DUP  
                           WHILE  2DUP S" \" COMPARE 
                                  0= IF  2DROP REFILL DROP
                                   ELSE  S $, 1 R@ +!  
                                  ENDIF
                           REPEAT 2DROP -R -S
                    ENDIF
        DOES>   CELL+ @+ 1+ ROT * + ( ix -- addr ) ; 

#15 CHARS =: /symbol
#15 CHARS =: /param 

/symbol SYMTAB KWlist   IF ELSE ENDIF   \ 
                        WHILE ENDWHILE  \ 
                        DO ENDDO        \
                        LOOP ENDLOOP    \ 
                        REPEAT UNTIL    \
                        FOR TO ENDFOR   \
                        BREAK           \
                        READ WRITE      \ 
                        VAR END         \
                        PROCEDURE       \
                        PROGRAM

: KW->token ( kw_index -- ) 2+ C" xilewedeLerufteBRWvepP" + C@ TO token ;
 
        /symbol  NEGATE SYMTAB SymT
        =CELL 1- NEGATE SYMTAB SymType
        /param   NEGATE SYMTAB Params
        =CELL 1- NEGATE SYMTAB ParType

0 SymT    2 CELLS - =: [cnt]SymT
0 Params  2 CELLS - =: [cnt]Params
0 SymType 2 CELLS - =: [cnt]SymType
0 ParType 2 CELLS - =: [cnt]ParType

: init.sym ( -- )
        [cnt]SymT    0!
        [cnt]SymType 0! ;

: lookup ( c-addr u 'table -- n2|-1 )
        0 0 LOCALS| /symbol n table sz addr |
        table 2 CELLS - @+ TO n  @ TO /symbol
        n 0<= IF  -1 EXIT  ENDIF
           0 n DO 
                  /symbol 1+ I * table + COUNT  
                  addr sz COMPARE 0= IF  I UNLOOP EXIT  ENDIF
         -1 +LOOP 
        -1 ;

: locate  ( c-addr u -- x ) 0 SymT lookup ;     -- Returns -1 | the index of the entry.
: intable ( c-addr u -- f ) 0 SymT lookup 0>= ; -- Look for symbol in table

: clearparams ( -- ) [cnt]Params 0!  [cnt]ParType 0! ;  -- Clear the parameter table
: paramnumber ( c-addr u -- u ) 0 Params lookup ;       -- Get parameter's index ( 1 ... )
: param?      ( c-addr u -- f ) paramnumber 0> ;        -- See if an identifier is a parameter 

: typeof ( c-addr u  -- char ) 
        2DUP param? IF  2DROP 'f' EXIT  ENDIF  ( In principle, 'F' could be returned )
        2DUP locate DUP 0< IF  DROP .undefined  ENDIF
        NIP NIP SymType C@ ; 

: checktable ( c-addr u -- ) 2DUP intable    IF 2DROP EXIT ENDIF .undefined ; -- Is identifier in the symbol table?
: checkdup   ( c-addr u -- ) 2DUP intable 0= IF 2DROP EXIT ENDIF .duplicate ; -- Is identifier already in symbol table?
: checkident ( -- )          'x' <>token IF  S" Identifier" expected  ENDIF ; -- Is current token an identifier?

: addentry ( c-addr u typ -- )
        [cnt]SymT LOCALS| #entries T sz addr |
        addr sz checkdup
        #entries @ maxentry = IF  S" Symbol table full" aborts  ENDIF
        1 #entries +!
        addr sz  #entries @ SymT     PACK DROP 
        T        #entries @ SymType  C! ;

: addparam ( c-addr u typ -- ) 
        [cnt]Params LOCALS| #entries T sz addr |
        addr sz param? IF  addr sz .duplicate  ENDIF
        #entries @ maxentry = IF  S" Parameter table full" aborts  ENDIF
        1 #entries +! ( base is 1 )
        addr sz #entries @ Params  PACK DROP 
        T       #entries @ ParType ! ;

: checkvar ( c-addr u -- v|V ) 
        2DUP intable 0= IF  .undefined  ENDIF
        2DUP typeof DUP 'v' <> OVER 'V' <> 
          AND IF  DROP S" is not a global variable" $aborts  
           ENDIF  NIP NIP ;

: checkpar ( index -- f|F ) 
        DUP ParType @ DUP 'f' <> OVER 'F' <> 
          AND IF  DROP (.) S" reference to non-local variable #" 
                  2SWAP $+ aborts  
           ENDIF  NIP ;

: .symbols ( -- )
        [cnt]SymT @ 0= IF  CR ." No symbols defined." EXIT  ENDIF
        CR ." -- type --.--- name ---" 
        [cnt]SymT @ 0 ?DO  CR   5 HTAB I 1+ SymType C@ EMIT 
                              #16 HTAB I 1+ SymT   .$ 
                     LOOP ;

        S" codegen.frt" INCLUDED 
WARNING @  WARNING OFF  

: digit?   ( char -- tf )  '0' '9' 1+ WITHIN ;

WARNING !

: alpha?   ( char -- tf )  >UPC 'A' 'Z' 1+ WITHIN ;
: alnum?   ( char -- tf )  DUP alpha? SWAP digit? OR ;
: orop?    ( char -- tf )  DUP '|' =  SWAP '~' =  OR ;
: mulop?   ( char -- tf )  DUP '*' =  SWAP '/' =  OR ;
: addop?   ( char -- tf )  DUP '+' =  SWAP '-' =  OR ;

: relop? ( char -- tf )  
        DUP  '=' = 
        OVER '<' = OR
        SWAP '>' = OR ;

: match ( char -- )
        DUP Look = IF  DROP getchar EXIT  ENDIF 
        S" `" ROT CHAR-APPEND &' CHAR-APPEND expected ;

: white? ( char -- tf )  
        DUP  Tab =  
        OVER BL  = OR
        OVER '{' = OR
        OVER ^M  = OR 
        SWAP ^J  = OR ; 

: skipcomment RECURSIVE ( -- )
        BEGIN   Look '}' <> 
        WHILE   getchar
                Look '{' = IF  skipcomment  ENDIF
        REPEAT  getchar ;

: skipwhite ( -- )
        BEGIN  Look white?
        WHILE  Look '{' = IF  skipcomment  ELSE  getchar  ENDIF
        REPEAT ;

: getname ( -- )
        skipwhite
        Look alpha? 0= IF  S" Identifier" expected  ENDIF
        'x' TO token
        token$ C0! 
        BEGIN
          Look token$ char+!  getchar
          Look alnum? 0=
        UNTIL ;

: getnumber ( -- )
        skipwhite
        Look digit? 0= IF  S" Number" expected  ENDIF
        '#' TO token
        token$ C0!
        BEGIN   
          Look token$ char+!  
          getchar
          Look digit? 0=
        UNTIL ;

: getop ( -- )
        skipwhite
        Look TO token 
        Look token$ char-place
        getchar ;

: (next) ( -- )
        skipwhite
        Look alpha? IF  getname   EXIT  ENDIF
        Look digit? IF  getnumber EXIT  ENDIF
        getop ;

: nextt debug? @ IF  CR ." next["  ENDIF
        (next)
        debug? @ 0= ?EXIT
        ." ]next token=`"  Token  EMIT ." ', token$=`" token> TYPE &' EMIT .S ;

: ?semi ( -- )  ';' =token IF  nextt  ENDIF ;

: iscan ( -- ) 'x' =token IF  token> $>UPC 0 KWlist lookup  KW->token  ENDIF ;

: matchstring ( c-addr u -- )
        token> $>UPC 2OVER COMPARE 0= IF  2DROP nextt EXIT  ENDIF
        &` CHAR-PREPEND &' CHAR-APPEND expected ;

: matchchar ( char -- )
        DUP token$ CHAR+ C@ >UPC = IF  DROP nextt EXIT  ENDIF
        S" `" ROT CHAR-APPEND &' CHAR-APPEND expected ;

DEFER boolexpression

: factor ( -- ) 
        '(' =token IF  nextt boolexpression  ')' matchchar  EXIT  ENDIF
        'x' =token IF  token> param? IF  token> paramnumber _parameter@
                                   ELSE  token> _variable@
                                  ENDIF  nextt EXIT
                ENDIF
        '^' =token IF  nextt token>
                              param? IF  token> paramnumber _paraddr
                                   ELSE  token> _varaddr
                                  ENDIF  nextt EXIT
                ENDIF
        '#' =token IF  token> _constant@  nextt  EXIT  ENDIF 
        S" Math factor" expected ;

: multiply  ( -- ) nextt  factor _popmul ;  
: divide    ( -- ) nextt  factor _popdiv ;

: term ( -- ) 
        factor 
        BEGIN   token mulop?
        WHILE   _push
                CASE token
                  '*' OF multiply  ENDOF
                  '/' OF divide    ENDOF
                ENDCASE 
        REPEAT ;

: add       ( -- ) nextt  term   _popadd ; 
: subtract  ( -- ) nextt  term   _popsub ;

: expression ( -- ) 
        token addop? IF  _clear 
                   ELSE  term
                  ENDIF
        BEGIN   token addop? 
        WHILE   _push
                CASE token
                  '+' OF add      ENDOF
                  '-' OF subtract ENDOF
                ENDCASE 
        REPEAT ;

: nextx       ( -- )  nextt expression ;

: equals      ( -- )  nextx _pcmpe ;
: lessorequal ( -- )  nextx _pcmple ;
: notequals   ( -- )  nextx _pcmpne ;

: less ( -- ) 
        nextt
        CASE token
          '=' OF  lessorequal    ENDOF
          '>' OF  notequals      ENDOF
                  expression _pcmpl 
        ENDCASE ;

: greater ( -- ) 
        nextt
        '=' =token IF  nextx _pcmpge EXIT  ENDIF
        expression _pcmpg ;

: relation ( -- )
        expression
        token relop? 0= ?EXIT
        _push
        CASE token
          '=' OF  equals     ENDOF
          '<' OF  less       ENDOF
          '>' OF  greater    ENDOF
        ENDCASE ;

: notfactor ( -- )
        '!' <>token IF  relation EXIT  ENDIF
        nextt relation _not ;

: boolterm ( -- )
        notfactor
        BEGIN   '&' =token 
        WHILE   _push nextt notfactor _popand
        REPEAT ;

: boolOR  ( -- ) nextt boolterm _popor ;
: boolXOR ( -- ) nextt boolterm _popxor ;

:NONAME ( -- )
        boolterm
        BEGIN   token orop?
        WHILE   _push
                CASE token
                  '|' OF  boolOR  ENDOF
                  '~' OF  boolXOR ENDOF
                ENDCASE
        REPEAT ; IS boolexpression

: assignment ( c-addr u -- )
        DUP 1+ ALLOCATE ?ALLOCATE DUP LOCAL name PACK DROP
        nextt  
        '=' matchchar
        boolexpression
        name COUNT param? IF  name COUNT paramnumber _parameter!
                        ELSE  name COUNT _variable!
                       ENDIF
        name FREE ?ALLOCATE ;

: param ( -- ) expression _push ;

: paramlist ( -- #bytes )
        0 LOCAL N
        nextt
        '(' matchchar
        ')' <>token
           IF   param 1 +TO N
                BEGIN ',' =token
                WHILE nextt param 1 +TO N
                REPEAT 
        ENDIF
        ')' matchchar
        N CELLS ;

: callproc ( c-addr u -- ) 
        DUP 1+ ALLOCATE ?ALLOCATE DUP >S PACK DROP
        paramlist >R  
          S COUNT _callw 
        R> _cleanstack 
        S> FREE ?ALLOCATE ;

: assignorproc ( -- )
        CASE token> typeof 
           0  OF  token> .undefined  ENDOF
          'v' OF  token> assignment  ENDOF
          'V' OF  token> assignment  ENDOF
          'f' OF  token> assignment  ENDOF
          'F' OF  token> assignment  ENDOF ( never should appear )
          'p' OF  token> callproc    ENDOF
              S" Identifier `" token> $+ 
              S" ' cannot be used here" $+ aborts 
        ENDCASE ;

DEFER pblock

: doblock ( -- )  
        BEGIN  iscan  'e' <>token '.' <>token AND  
        WHILE  -1 pblock  
        REPEAT ;

: beginblock ( -- )  
        S" BEGIN" matchstring  
          doblock  
        S" END"   matchstring ;

: doMain ( -- )
        S" PROGRAM" matchstring  token> prog$ PACK DROP  nextt ?semi
        _prolog  beginblock  _epilog ;

: doIF ( label -- )
        -1 -1 LOCALS| L2 L1 L |
        nextt
        boolexpression
        assembly?  IF   newlabel TO L1
                        L1 TO L2
                        L1 _branch0
                 ELSE   S"    IF  " emit2lns
                ENDIF
        L pblock
       'l' =token IF   nextt
                        assembly? IF  newlabel TO L2
                                      L2 _branch
                                      L1 postlabel
                                ELSE  S"  ELSE  " emit2lns
                               ENDIF
                        L pblock
                ENDIF
        assembly?  IF   L2 postlabel
                 ELSE   S" ENDIF  " emitdln
                ENDIF
        S" ENDIF" matchstring ;

: doWHILE ( -- )
        -1 -1 LOCALS| L2 L1 |
        assembly?  IF   newlabel TO L1
                        newlabel TO L2
                        nextt
                        L1 postlabel
                 ELSE   S" BEGIN  " emitdln
                        nextt
                ENDIF
        boolexpression
        assembly?  IF   L2 _branch0
                 ELSE   S" WHILE  " emitdln
                ENDIF
        L2 pblock
        S" ENDWHILE" matchstring
        assembly?  IF   L1 _branch
                        L2 postlabel
                 ELSE   S" REPEAT " emitdln 
                ENDIF ;

: doLOOP ( -- )
        -1 -1 LOCALS| L2 L1 |
        assembly?   IF  newlabel TO L1
                        newlabel TO L2
                  ELSE  S" BEGIN  " emitdln
                 ENDIF
        nextt
        assembly?   IF  L1 postlabel
                        L2 pblock
                        L1 _branch
                        L2 postlabel
                  ELSE  L2 pblock
                        S" AGAIN  " emitdln
                 ENDIF
        S" ENDLOOP" matchstring ;

: doREPEAT ( -- )
        -1 -1 LOCALS| L2 L1 |
        assembly?   IF  newlabel TO L1
                        newlabel TO L2
                        nextt
                        L1 postlabel
                  ELSE  S" BEGIN  " emitdln
                        nextt
                 ENDIF
        L2 pblock
        S" UNTIL" matchstring
        boolexpression
        assembly?   IF  L1 _branch0
                        L2 postlabel 
                  ELSE  S" UNTIL" emitdln 
                 ENDIF ;

: doFOR ( -- )
        -1 -1 -1 LOCALS| name L2 L1 |
        nextt
        checkident  token> checktable
        token>   DUP 1+ ALLOCATE ?ALLOCATE DUP TO name PACK DROP
        newlabel TO L1
        newlabel TO L2

        nextt  '=' matchchar  expression
        _decr
        name COUNT _variable!
        S" TO" matchstring  
        expression
        _push
        L1 postlabel
        name COUNT _variable@
        _incr
        name COUNT _variable!
        L2 _pcmp+b0>
        L2 pblock
        L1 _branch
        L2 postlabel
        S" ENDFOR" matchstring
        _incSP

        name FREE ?ALLOCATE ;

: doDO ( -- )
        -1 -1 LOCALS| L2 L1 |
        newlabel TO L1
        newlabel TO L2

        nextt
        expression
        L1 postlabel
        _push
        L2 pblock
        _pop
        _decr
        L1 _branch<>0
        _decSP
        L2 postlabel
        S" ENDDO" matchstring
        _incSP ;

: doBREAK ( label -- )
        DUP 0< IF  DROP S" No loop to break from" aborts  ENDIF
        assembly? IF  _branch 
                ELSE  DROP S" BREAK" emitdln
               ENDIF
        nextt ;

: readvar ( -- ) checkident  token> checktable  token> _readit  nextt ;

: doread ( -- )
        nextt 
        '(' matchchar
        readvar
        BEGIN  ',' =token
        WHILE  nextt readvar
        REPEAT 
        ')' matchchar ;

: dowrite ( -- )
        nextt 
        '(' matchchar
        expression _writeit
        BEGIN  ',' =token
        WHILE  nextt expression _writeit
        REPEAT 
        ')' matchchar ;

:NONAME ( label -- )
        LOCAL L
        BEGIN   iscan
                'e' <>token 
                'l' <>token AND
                'u' <>token AND
        WHILE  CASE token
                'i' OF  L doIF    ENDOF
                'w' OF  doWHILE   ENDOF
                'd' OF  doDO      ENDOF
                'L' OF  doLOOP    ENDOF
                'r' OF  doREPEAT  ENDOF
                'f' OF  doFOR     ENDOF
                'B' OF  L doBREAK ENDOF
                'R' OF  doread    ENDOF
                'W' OF  dowrite   ENDOF
                        assignorproc
               ENDCASE
               ?semi
        REPEAT ; IS pblock

: formalparam ( -- ) 
        '@' =token IF  'F' nextt  ELSE  'f'  ENDIF
        token> ROT addparam ;

: formallist ( -- )
        nextt 
        '(' matchchar
        ')' <>token 
           IF   formalparam
                BEGIN  nextt ',' =token 
                WHILE  nextt formalparam
                REPEAT
        ENDIF
        ')' matchchar  
        [cnt]Params @ TO lbase 
        2 [cnt]Params +! ;

: locdecl ( -- )  token> 'f' addparam  nextt ;

: (locdecls) ( n1 -- n2 )
        iscan 'v' <>token ?EXIT
        BEGIN  nextt  locdecl 1+  ',' <>token  UNTIL 
        ?semi ;

: locdecls ( -- n )  0 BEGIN (locdecls) iscan 'v' <>token UNTIL ;

: doProc ( -- )
        nextt 
        token> DUP 1+ ALLOCATE ?ALLOCATE PACK >R 
        R@ COUNT 'p' addentry
        formallist
        locdecls ( #formals )
        R@ COUNT _procprolog
        R> FREE ?ALLOCATE
        beginblock
        _procepilog
        clearparams ;

: alloc ( -- )
        '@' =token IF  'V' nextt  ELSE  'v'  ENDIF
        token> DUP 1+ ALLOCATE ?ALLOCATE DUP >S PACK DROP
        'x' <>token IF  S" Variable name" expected  ENDIF
        S COUNT ROT addentry
        nextt
        '=' =token IF   '=' matchchar
                        '-' =token IF  '-' matchchar
                                       S" -" token> $+       ( ** )
                                 ELSE  token> BL CHAR-APPEND ( ** )
                                ENDIF  ( c-addr u ) 
                        nextt
                 ELSE   S" 0"
                ENDIF   ( c-addr u ) 
        S COUNT  allocatestorage 
        S> FREE ?ALLOCATE ;

: decl ( -- ) 
        nextt alloc  
        BEGIN  ',' =token WHILE  nextt alloc  REPEAT ;

: topdecls ( -- )
        BEGIN   '.' <>token
        WHILE   CASE iscan token
                  'v' OF  decl   ENDOF
                  'p' OF  doProc ENDOF
                  'P' OF  doMain ENDOF
                      S" Unrecognized keyword" token> $aborts
                ENDCASE
                ?semi
        REPEAT ;

: init ( -- ) 
        init.output
        init.code
        init.error
        init.sym
        clearparams
        _header
        init.input nextt ; 

: COMPILER ( -- ) init topdecls ;

: CI ( -- ) COMPILER ;

:ABOUT  CR ." Try:   compiler <input text> -- compile text" 
        CR ." or:    ci       <input text> -- compile text" 
        CR ." Also:  .SYMBOLS              -- dump symbol table"
        CR ." Try:   compiled? OFF | ON    -- list / compile"
        CR ." See the documentation for a BNF."
        CR
        CR ." Example input:"
        CR
        CR ." var a=22,b=-2;"
        CR
        CR ." procedure foo(@x,y)"
        CR ." begin a=x+y end;"
        CR
        CR ." var c=111;"
        CR
        CR ." program test; { a test { obviously } }"
        CR ." begin"
        CR ."   if a&!b|!a&b"
        CR ."         foo(^a, a+b);
        CR ."         write(a*2+b,b+3/a,c)"
        CR ."   endif" 
        CR ." end." 
        CR ;

                DEPRIVE
                .ABOUT -compiler CR

