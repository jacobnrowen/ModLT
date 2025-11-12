{
{-# OPTIONS_GHC -w #-}
module TDucLexer(Token(..), lexTDuc, testLexTDuc) where
import Data.Char
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
@assign = ":="
@spaces = [\ \t]*
$matchAny = \0-\256
@alphaVarName = [$alpha \_][$alpha $digit \_]*
$symbol = [\! \# \$ \% \& \* \+ \- \. \/ \: \; \< \= \> \? \@ \^ \_ \| \~]
@arityBlock = @spaces "," @spaces "_" @spaces
@padding = $white*



tokens :-

    ("--" | "//").*  ;  --single line comment
    "/*" $matchAny* "*/"  ;  --block comment
    @padding "#Recipes" @padding {\s -> RecHead}  --header for Recipes
    @padding "Signature" @padding  {\s -> SigHead}  --header for Signature
    @padding "Formulas" @padding  {\s -> FmlasHead}  --header for Formulas
    "DOM"  {\s -> DomToken}  --for defining the domain
    "CSET" @spaces @assign @spaces $digit+  {\s -> CsetToken (getNum s)}  --defines the size of the copy set
    "LIC"  {\s -> LicToken}  --for indicating a licensing formula
    $digit+  {\s -> RelNumToken (read s)}  --for the indication of which copy sets a relation is being defined on
    "{" @padding  {\s -> OpenCurly}  --section starter
    "}" @padding  {\s -> CloseCurly}  --section ender
    "("  {\s -> OpenParen}  --multiple uses
    ")"  {\s -> CloseParen}  --multiple uses
    "["  {\s -> OpenBrack}  --quantified expression scope starter
    "]"  {\s -> CloseBrack}  --quantified expression scope ender
    "(" @spaces "_" @arityBlock* ")"  {\s -> ArityToken (length $ filter (== '_') s)}  --arity indication
    ","  ;  --argument separator
    @assign  {\s -> AssignToken}  --assignment operator
    "true" | "True" | "TRUE"  {\s -> TrueToken}  --the true literal
    "false" | "False" | "FALSE" {\s -> FalseToken}  --the false literal
    "~"  {\s -> NotToken}  --negation operator for formulas; the only 1-arity operator
    "||" | "&&" | "->" | "<->"  {BinOpToken}  --binary operators for formulas
    "="  {\s -> EqualSign}
    "\E" | "\A" | "\ESET" | "\ASET"  {QuantifierToken}  --quantifiers for formulas
    "\ELEM"  {\s -> ElemOfToken}
    @alphaVarName  {AlphaVarName}  --recipe, variable, or relation name (non-symbolic)
    "\SET" @spaces "(" @spaces @alphaVarName @spaces ")"  {\s -> SetVarName (getVar s)}  --defining a set variable
    $symbol [$symbol $digit]*  {SymbolVarName}  --symbolic relation name
    $white+  {checkNewLine}  --check if there's a new line in the whitespace
    

{

data Token
    = RecHead
    | SigHead
    | FmlasHead
    | DomToken
    | CsetToken Int
    | LicToken
    | RelNumToken Int
    | OpenCurly
    | CloseCurly
    | OpenParen
    | CloseParen
    | OpenBrack
    | CloseBrack
    | ArityToken Int
    | AssignToken
    | TrueToken
    | FalseToken
    | NotToken
    | BinOpToken String
    | EqualSign
    | QuantifierToken String
    | ElemOfToken
    | AlphaVarName String
    | SetVarName String
    | SymbolVarName String
    | LineSep
    | EmptyToken
    deriving (Eq, Show)


lexTDuc :: String -> [Token]
lexTDuc s = result
    where
        rawToks = alexScanTokens s
        noEmpty = (filter (/=EmptyToken) rawToks) ++ [LineSep]
        result = case reverse (cleanLineSeps [] noEmpty) of
            LineSep:rest -> rest --We want to remove a stream-initial LineSep if it's there
            toks -> toks
        --We want to boil each LineSep down to just one
        cleanLineSeps acc [] = acc
        cleanLineSeps [] (t:ts) = cleanLineSeps [t] ts
        cleanLineSeps (prev:rest) (t:ts) = if t == LineSep && 
            (prev == LineSep || prev == CloseCurly) then 
            cleanLineSeps (prev:rest) ts else cleanLineSeps (t:(prev:rest)) ts


checkNewLine :: String -> Token
checkNewLine s = if length (filter (=='\n') s) > 0 then LineSep else EmptyToken

getNum :: String -> Int
getNum s = read digs
    where
        digs = findDigs s
        findDigs [] = undefined
        findDigs (c:rest) = if (ord c >= ord '0' && ord c - ord '0' <= 9) then (c:rest) else findDigs rest

getVar :: String -> String
getVar s = takeWhile notClose (dropWhile openOrSpace (drop 5 s))
    where
        openOrSpace c = c == ' ' || c == '\t' || c == '('
        notClose c = c /= ')'

testLexTDuc = do
    s <- readFile "../test/example1.txt"
    putStrLn (show (lexTDuc s))
}