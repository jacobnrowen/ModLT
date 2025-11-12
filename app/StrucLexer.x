{
{-# OPTIONS_GHC -w #-}
module StrucLexer (Token(..), lexStrucs, testLexStrucs) where
import Data.Char
}

%wrapper "basic"

$digit = 0-9
@spaces = [\ \t]*
@padding = $white*
$symbol = [\! \# \$ \% \& \* \+ \- \. \/ \: \; \< \= \> \? \@ \^ \_ \| \~]
@name = [a-z A-Z $symbol] [a-z A-Z $symbol $digit]*
@arityBlock = @spaces "," @spaces "_" @spaces
$any = [\x00-\x10ffff] --literally any Unicode symbol
$strucString = $any # [\} \{]
$alphaString = $strucString # $white


tokens :-

    "Signature"  {\s -> SigHead}  --header for Signature
    "AlphaMapTable"  {\s -> AlphaMapHead}  --header for AlphaMapTable
    "StringOrders"  {\s -> OrdersHead}  --header for StringOrders
    "succ:"  {\s -> SuccHead}  --indication that a StringOrder is successor-style
    "prec:"  {\s -> PrecHead}  --indication that a StringOrder is precedence-style
    @name  {\s -> RelOrStrucName s}  --the name of a Relation or Structure
    "(" @spaces "_" @arityBlock* ")"  {\s -> ArityToken (length $ filter (== '_') s)}  --arity indication
    "Size:" @spaces $digit+  {\s -> getSizeToken s}  --indicates the size of a Structure
    $digit+  {\s -> DomElemToken (read s)}  --a particular domain element
    "][" @spaces $alphaString+  {\s -> getAlphaString s}  --the string mapped to by an AlphaMapRule
    "{"  {\s -> OpenCurly}  --section starter
    "}"  {\s -> CloseCurly}  --section ender
    "["  {\s -> OpenBrack}  --multiple uses
    "]"  {\s -> CloseBrack}  --multiple uses
    "#String" $strucString+  {\s -> getStrucString s}  --A Structure defined in String format
    $white | \,  ;  --whitespace and item separators  




{

data Token
    = SigHead
    | AlphaMapHead
    | OrdersHead
    | SuccHead
    | PrecHead
    | RelOrStrucName String
    | ArityToken Int
    | SizeToken Int
    | DomElemToken Int
    | RawString String
    | OpenCurly
    | CloseCurly
    | OpenBrack
    | CloseBrack
    deriving (Eq, Show)

lexStrucs = alexScanTokens

getSizeToken :: String -> Token
getSizeToken "" = SizeToken 0 --cannot happen
getSizeToken (c:cs) = if isDigit c then SizeToken (read (c:cs)) else getSizeToken cs

getAlphaString :: String -> Token
getAlphaString "" = RawString "" --cannot happen
getAlphaString (c:cs) = if c `elem` "][ \t" then getAlphaString cs 
                        else RawString (c:cs)

getStrucString :: String -> Token
getStrucString s = RawString (rstrip trimStart)
    where
        trimStart = dropWhile (\c -> c `elem` "#String" || isSpace c) s
        rstrip = reverse . lstrip . reverse --Taken from Data.String.Utils
        lstrip s = case s of
            "" -> ""
            (c:cs) -> if isSpace c then lstrip cs else s

testLexStrucs = do
    s <- readFile "../test/example2.txt"
    putStrLn (show (lexStrucs s))
}