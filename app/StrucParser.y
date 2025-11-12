{
{-# OPTIONS_GHC -w #-}
module StrucParser (parseStrucs) where
import StrucLexer
import Data.Set
import Types

}

%name runStrucsParser
%tokentype { Token }

%error { (\tk -> error ("parse error: " ++ (show tk))) }

%expect 0

%token

    sigHead     { SigHead }
    alphaHead   { AlphaMapHead }
    ordersHead  { OrdersHead }
    succ        { SuccHead }
    prec        { PrecHead }
    name        { RelOrStrucName $$ }
    arity       { ArityToken $$ }
    size        { SizeToken $$ }
    domElem     { DomElemToken $$ }
    rawStr      { RawString $$ }
    '{'         { OpenCurly }
    '}'         { CloseCurly }
    '['         { OpenBrack }
    ']'         { CloseBrack }

%%

--Top Level Final Product
StrucsFile :: {ParsedStrucsFile}  :
    Signature AlphaMapTable Structures {ParsedStrucsFile $1 $2 (reverse $3)}

--Signature Stuff
Signature :: {[SigRelation]}  :
    sigHead '{' RelArities '}'  {$3}
    |  {- empty -}               {[]}

RelArities :: {[SigRelation]} :
    RelAndArity                 {[$1]}
    |  RelArities RelAndArity   {$2 : $1}

RelAndArity :: {SigRelation}  :
    name arity          {SigRelation $1 $2}



--AlphaMapTable Stuff
AlphaMapTable :: {Maybe AlphaMapTable}  :
    alphaHead '{' AlphaMapRules '[' rawStr '}'  {Just (AlphaMapTable (reverse $3) $5)}
    |  {- empty -}                              {Nothing}

AlphaMapRules :: {[AlphaMapRule]}  :
    AlphaMapRule                    {[$1]}
    |  AlphaMapRules AlphaMapRule   {$2 : $1}

AlphaMapRule :: {AlphaMapRule}  :
    '[' AlphaMapRels rawStr  {($2, $3)}

AlphaMapRels :: {Set String}  :
    name                    {singleton $1}
    |  AlphaMapRels name     {singleton $2 `union` $1}


--Structures Stuff
Structures :: {[ParsedStruc]}  :
    {- empty -}             {[]}
    |  Structures Structure {$2 : $1}

Structure :: {ParsedStruc}  :
    StrucName '{' StringOrders StrucSize StrucRels '}'  {ParsedStruc $1 $3 $4 (Left $5)}
    |  StrucName '{' rawStr '}'                 {ParsedStruc $1 [] Nothing (Right $3)}

StrucName :: {Maybe String}  :
    name            {Just $1}
    |  {- empty -}  {Nothing}

StringOrders :: {[StringOrder]}  :
    ordersHead '{' Orders '}'   {$3}
    |  {- empty -}              {[]}

Orders :: {[StringOrder]}  :
    Order               {[$1]}
    |  Orders Order     {$2 : $1}

Order :: {StringOrder}  :
    succ name       {StringOrder $2 SuccOrder []}
    |  prec name    {StringOrder $2 PrecOrder []}

StrucSize :: {Maybe Int}  :
    size            {Just $1}
    |  {- empty -}  {Nothing}

StrucRels :: {[(String, [RMember])]}  :
    StrucRel                {[$1]}
    |  StrucRels StrucRel   {$2 : $1}

StrucRel :: {(String, [RMember])}  :
    name '[' Members ']'    {($1, $3)}

Members :: {[RMember]}  :
    {- empty -}         {[]}
    |  Members Member   {$2 : $1}

Member :: {RMember}  :
    '[' DomElems ']'    {reverse $2}

DomElems :: {RMember}  :
    domElem                 {[$1]}
    |  DomElems domElem     {$2 : $1}



{

parseStrucs :: String -> ParsedStrucsFile
parseStrucs s = runStrucsParser (lexStrucs s)

}