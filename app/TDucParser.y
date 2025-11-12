{
{-# OPTIONS_GHC -w #-}
module TDucParser (parseTDuc) where
import TDucLexer
import Types (
    ParsedTDuc(..),
    RecipeCall(..),
    FormulaVar(..),
    FormulaDef(..),
    LicDef(..),
    RelMappingDef(..),
    SigRelation(..),
    MSOFormula(..),
    )
}

%name runTDucParser
%tokentype { Token }

%error { (\tk -> error ("parse error: " ++ (show tk))) }
%expect 2  --We expect a couple ambiguities with line separation that should not matter

%token

    recHead     { RecHead }
    sigHead     { SigHead }
    fmlasHead   { FmlasHead }
    dom         { DomToken }
    csetsz      { CsetToken $$ }
    lic         { LicToken }
    relNum      { RelNumToken $$ }
    '{'         { OpenCurly }
    '}'         { CloseCurly }
    '('         { OpenParen }
    ')'         { CloseParen }
    '['         { OpenBrack }
    ']'         { CloseBrack }
    arity       { ArityToken $$ }
    ":="        { AssignToken }
    true        { TrueToken }
    false       { FalseToken }
    not         { NotToken }
    binop       { BinOpToken $$ }
    '='         { EqualSign}
    elemOf      { ElemOfToken }
    quantifier  { QuantifierToken $$ }
    alphaVar    { AlphaVarName $$ }
    setVar      { SetVarName $$ }
    symbolVar   { SymbolVarName $$ }
    '\n'        { LineSep }


%right binop
%right not
%nonassoc elemOf
%right symbolVar
%right '='

%%
--Top Level Final Product
Transduction :: {ParsedTDuc} :
    Recipes Signature Formulas Domain Cset Licensors Relations FileEdge {ParsedTDuc $1 $2 $3 $4 $5 $6 $7}

FileEdge :: {()} :
    {-empty -}  {()}
    |  '\n'     {()}


--Recipe Stuff
Recipes :: {[RecipeCall]}  :
    recHead '{' RecipeCalls '}'  {reverse $3}
    | {- empty -}                {[]}

RecipeCalls :: {[RecipeCall]}  :
    Recipe                  {[$1]}
    |  RecipeCalls Recipe   {$2 : $1}

Recipe :: {RecipeCall}  :
    alphaVar '(' RecipeArgs ')'  {RecipeCall $1 (reverse $3)}
    |  alphaVar '(' RecipeArgs ')' '\n'  {RecipeCall $1 (reverse $3)}

RecipeArgs :: {[String]}  :
    {- empty -}  {[]}
    |  RecipeArgs RecipeArg {$2 : $1}

RecipeArg :: {String}  :
    RelOrFmlaName  {$1}
    |  '\n' RelOrFmlaName  {$2}
    |  RelOrFmlaName '\n'  {$1}
    |  '\n' RelOrFmlaName '\n'  {$2} 


--Signature Stuff
Signature :: {[SigRelation]}  :
    sigHead '{' RelArities '}'  {$3}
    | {- empty -}               {[]}

RelArities :: {[SigRelation]} :
    RelAndArity                 {[$1]}
    |  RelArities RelAndArity   {$2 : $1}

RelAndArity :: {SigRelation}  :
    RelOrFmlaName arity          {SigRelation $1 $2}
    |  RelOrFmlaName arity '\n'  {SigRelation $1 $2}

--Formulas Stuff
Formulas :: {[FormulaDef]}  :
    fmlasHead '{' AllFormulas '}'  {$3}
    |  {- empty -}                 {[]}

AllFormulas :: {[FormulaDef]}  :
    {- empty -}             {[]}
    |  AllFormulas Formula  {$2 : $1}

Formula :: {FormulaDef}  :
    alphaVar '(' FmlaArgList ')' ":=" MSOBody '\n'  {FormulaDef $1 (reverse $3) $6}

FmlaArgList :: {[FormulaVar]}  :
    {-empty -}              {[]}
    |  FmlaArgList alphaVar     {(ElemVar $2) : $1}
    |  FmlaArgList setVar       {(SetVar $2) : $1}

--Domain stuff
Domain :: {Maybe MSOFormula}  :
    dom ":=" MSOBody '\n'  {Just $3}
    |  {- empty -}         {Nothing}

--Cset stuff
Cset :: {Int}  :
    csetsz '\n'     {$1}
    |  {- empty -}  {1} --If no copy set size provided, assume a size of 1

--Licensors stuff
Licensors :: {[LicDef]}  :
    {-empty -}        {[]}
    |  Licensors Lic  {$2 : $1}

Lic :: {LicDef}  :
    lic '(' alphaVar ')' '(' relNum ')' ":=" MSOBody '\n'  {LicDef $3 $6 $9}
    |  lic '(' alphaVar ')' ":=" MSOBody '\n'              {LicDef $3 1 $6}

--Relations stuff
Relations :: {[RelMappingDef]}  :
    {-empty -}           {[]}
    |  Relations RelDef  {$2 : $1}

RelDef :: {RelMappingDef}  :
    RelOrFmlaName '(' ArgList ')' '(' RelNumList ')' ":=" MSOBody '\n'  {RelMappingDef $1 (reverse $3) (reverse $6) $9}
    |  RelOrFmlaName '(' ArgList ')' ":=" MSOBody '\n'                  {RelMappingDef $1 (reverse $3) [] $6}

RelNumList :: {[Int]}  :
    relNum                  {[$1]}
    |  RelNumList relNum    {$2 : $1}


--Useful productions used in multiple places
RelOrFmlaName :: {String}  :
    alphaVar    {$1}
    | symbolVar {$1}

ArgList :: {[String]}  :
    {-empty -}              {[]}
    |  ArgList alphaVar     {$2 : $1}

MSOBody :: {MSOFormula}  :
    true                                            {LitTrue}
    |  false                                        {LitFalse}
    |  not MSOBody                                  {Not $2}
    |  MSOBody binop MSOBody                        {getBinOp $1 $2 $3}
    |  EqualChain alphaVar                          {equalChain $1 $2}
    |  alphaVar elemOf alphaVar                     {ElemOf $1 $3}
    |  quantifier '(' ArgList ')' '[' MSOBody ']'   {getQuantifier $1 (reverse $3) $6}
    |  RelOrFmlaName '(' ArgList ')'                {Rel $1 (reverse $3)} --NOTE THIS COULD BE FORMULA TOO NEEDS POST PROCESSING
    |  SymbolChain alphaVar                         {symbolChain (reverse $1) $2}
    |  '(' MSOBody ')'                              {$2}

EqualChain :: {[String]}  :
    alphaVar '='                {[$1]}
    |  EqualChain alphaVar '='  {$2 : $1}

SymbolChain :: {[(String, String)]}  :
    alphaVar symbolVar                  {[($1, $2)]}
    |  SymbolChain alphaVar symbolVar   {($2, $3) : $1}



{

parseTDuc :: String -> ParsedTDuc
parseTDuc s = runTDucParser (lexTDuc s)

getBinOp :: MSOFormula -> String -> MSOFormula -> MSOFormula
getBinOp f1 op f2
    | op == "||"  = Or f1 f2
    | op == "&&"  = And f1 f2
    | op == "->"  = Implies f1 f2
    | otherwise   = Iff f1 f2

getQuantifier :: String -> [String] -> MSOFormula -> MSOFormula
getQuantifier q [] fmla  = undefined
getQuantifier q [v] fmla = (getQHelper q) v fmla
getQuantifier q (v:vs) fmla = (getQHelper q) v (getQuantifier q vs fmla)

getQHelper :: String -> (String -> MSOFormula -> MSOFormula)
getQHelper s
    | s == "\\E"    = Exists
    | s == "\\A"    = Forall
    | s == "\\ESET" = Exists2
    | otherwise     = Forall2

equalChain :: [String] -> String -> MSOFormula
equalChain [] _ = undefined
equalChain [v1] v2 = Equals v1 v2
equalChain (v1:rest) v2 = And (Equals v1 v2) (equalChain rest v2)
--a=b=c=d is being evaluated as (a=d) && (b=d) && (c=d) instead of
--the possibly more intuitive (a=b) && (b=c) && (c=d) because
--they are equivalent and the code is simpler this way

symbolChain :: [(String, String)] -> String -> MSOFormula
symbolChain [] _ = undefined
symbolChain [(v1, r)] v2 = Rel r [v1, v2]
symbolChain ((v1, r) : ((v2, r2) : rest)) v3 = And cur andRest
    where
        cur = (Rel r [v1, v2])
        andRest = symbolChain ((v2, r2):rest) v3
}