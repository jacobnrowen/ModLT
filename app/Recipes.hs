module Recipes (applyRecipes) where

import Types
import Data.Set
import qualified Data.Maybe
import Data.List (find)

procError :: [Char] -> a
procError msg = error ("Error:\n" ++ msg)

applyRecipes :: [RecipeCall] -> ProcessedTDuc -> ProcessedTDuc
applyRecipes recNames = Prelude.foldr (.) id (reverse (Prelude.map getRecipe recNames))
    where
        getRecipe :: RecipeCall -> (ProcessedTDuc -> ProcessedTDuc)
        getRecipe (RecipeCall name args)
            | name == "faithful"            = fillTransductionFaithful []
            | name == "colOrderPreserve"    = fillTDucColOrdPresrv args
            | name == "strictChecks"        = strictCheck []
            --ADD YOUR RECIPE HERE!
            | otherwise                 = procError ("Unrecognized recipe name " ++ name)


fillTransductionFaithful :: Recipe
--This function takes the ingredients of a transduction and fills in that which is not yet defined with defaults
--such that the resulting transduction is as close to the identity as possible.
--The default domain is true, cSetSize is 1, licnesing formula is true, and relation is faithful when
--  arguments are from the first copy set, faithful for relations with an arity of 1, and False for
--  relations with an arity greater than one where any argument is not from the first copy set.
--The TDucRelations can be missing TDucRelMappings, and they will be filled in as specified above.
--This function assumes that if the copy set size is not defined, then it's 1.
--If a larger copy set is desired, it must be passed explicitly, and
--  the length of the list of licensors must either match the copy set size or be empty
fillTransductionFaithful _ (ProcessedTDuc sig dom csize mLics mTDucRels) = result
    where
        result = ProcessedTDuc sig dom csize (Prelude.map Just lics) tducrels

        lics
            | Prelude.null mLics    = replicate csize ("", LitTrue)
            | otherwise             = Prelude.map (Data.Maybe.fromMaybe ("",LitTrue)) mLics

        tducrels
            | mTDucRels == empty    = Data.Set.map (makeFaithfulTDucRel csize) sig
            | otherwise             = Data.Set.unions [fullyDefined, fromNothing, fromPartial]

        definedNames = Data.Set.map relationName mTDucRels
        definedSigRs = Data.Set.filter (\sigr -> sigRname sigr `member` definedNames) sig

        (fullyDefined,partialDefined) = Data.Set.partition isValidTDucRelation mTDucRels
        fromNothing = Data.Set.map (makeFaithfulTDucRel csize) (Data.Set.filter (\s -> not (member s definedSigRs)) sig)
        fromPartial = Data.Set.map fillIn partialDefined

        fillIn :: TDucRelation -> TDucRelation
        fillIn (TDucRelation relnm fmlas) = if Prelude.null fmlas then makeFaithfulTDucRel csize sigRel else
                                            TDucRelation relnm (first:rest)
            where
                sigRel = Data.Set.elemAt 0 (Data.Set.filter (\s -> sigRname s == relnm) sig)
                first = Data.Maybe.fromMaybe (makeRelMap fthflFmla ones) (find' ones)
                rest = Prelude.map (fillRest (if ar == 1 then fthflFmla else LitFalse)) (tail allMps)

                ar = arity sigRel
                ones = replicate ar 1
                find' csetArgs = find (\rel -> fst (mapping rel) == csetArgs) fmlas
                allMps = sequence (replicate (arity sigRel) [1..csize])
                (relArgs,fthflFmla) = makeFaithfulMSOFormula sigRel
                makeRelMap :: MSOFormula -> [Int] -> TDucRelMapping
                makeRelMap msoFmla csetArgs = TDucRelMapping relArgs (csetArgs, msoFmla)
                fillRest :: MSOFormula -> [Int] -> TDucRelMapping
                fillRest msoFmla csetArgs = Data.Maybe.fromMaybe (makeRelMap msoFmla csetArgs) (find' csetArgs)

fillTDucColOrdPresrv :: Recipe
--This function calls fillTransductionFaithful after handling the relations that encode order,
--preserving that order by calling makeColOrdPresrvTDucRel for each ordering relation.
--As such, it requires that the size of the copy set and the licensing functions be defined.
fillTDucColOrdPresrv ordrRels (ProcessedTDuc sig dom csize mLics mTDucRels) = result
    where
        result = fillTransductionFaithful [] (ProcessedTDuc sig dom csize lics resTDucRels)
        lics = Prelude.map (\f -> Just ("(licV)", f)) licFmlas
        licFmlas = getLics mLics
        getLics :: [Maybe (String, MSOFormula)] -> [MSOFormula]
        getLics [] = []
        getLics (l:ls) = case l of
            Nothing -> procError "Column order preservation requires all licensing formulas to be explicitly specified"
            Just (_, fmla) -> fmla : getLics ls

        orders = makeOrders ordrRels
        makeOrders :: [String] -> Set StringOrder
        makeOrders [] = 
            procError "Column order preservation requires at least one order to preserve"
        makeOrders [_] = 
            procError ("Column order preservation requires a list of orders of the form: " ++
                        "{ordTyp1}, {relName1}, {ordTyp2}, {relName2}...")
        makeOrders [ordTyp, relName] = makeOneOrder ordTyp relName
        makeOrders (ordTyp:(relName:rest)) = makeOneOrder ordTyp relName `union` makeOrders rest
        makeOneOrder typ nm 
            | nm `notElem` sigRNames = procError ("Column order preservation given " ++ 
                "non-existent relation name: " ++ nm)
            | typ == "succ" = singleton (StringOrder nm SuccOrder [])
            | typ == "prec" = singleton (StringOrder nm PrecOrder [])
            | otherwise     = procError ("Valid order types for column order preservation" ++ 
                "are \"succ\" or \"prec\"; given: " ++ typ)
        sigRNames = Data.Set.map sigRname sig
        resTDucRels = mTDucRels `union` ordTDucRels
        ordTDucRels = Data.Set.map (\ordr -> makeColOrdPresrvTDucRel csize ordr ("(licV)", licFmlas)) orders


strictCheck :: Recipe
--This recipe ensures that the user explicitly defined all of
--the licensing functions and the domain of their transduction
strictCheck _ (ProcessedTDuc sig dom csize mLics mTDucRels) = ProcessedTDuc sig dom' csize mLics' mTDucRels
    where
        dom' = case dom of
            Nothing -> procError "Transduction domain is not explicitly specified, and checking is strict"
            d -> d
        mLics' = checkLics (1::Int) mLics
        checkLics _ [] = []
        checkLics cset (l:ls) = case l of
            Nothing -> procError ("Licensing function " ++ show cset ++ " is not explicitly specified, "
                ++ "and checking is strict")
            lic -> lic : checkLics (cset+1) ls



------------------------Helper functions-----------------------------



makeColOrdPresrvTDucRel :: Int -> StringOrder -> (String, [MSOFormula]) -> TDucRelation
--Given the size of the copy set, the ordering relation of the structure, and the licensing formulas,
--build a TDucRelation that does order preservation by column, i.e. glues elements from the copy set
--into the order between the domain element they copy and the following domain element
--ASSUMES:
--      -The StringOrder is with successor or precedence, not Custom
--      -The licensing formulas use the same bound variable name
makeColOrdPresrvTDucRel csetsz (StringOrder rname ordTyp _) (licVar, lics) = TDucRelation resName fmlas
    where
        resName
          | rname /= "" = rname
          | ordTyp == SuccOrder = "*"
          | otherwise = "<"
        fmlas :: [TDucRelMapping]
        fmlas = if ordTyp == SuccOrder then forSucc else forPrec
        a = licVar
        b = '2':licVar
        relArgs = [a, b]
        forSucc = oneOne:(downs++toOne++samesUp)
            where
                oneOne = TDucRelMapping relArgs ([1,1], And (Rel resName relArgs) (noneBelow 1))
                downs = [TDucRelMapping relArgs ([n1,n2], And (Equals a b) (noneAboveBetween n1 n2)) |
                            n1 <- [1..csetsz-1], n2 <- [2..csetsz], n1 < n2]
                toOne = Prelude.map (\n -> TDucRelMapping relArgs ([n,1], And (Rel resName relArgs) (noneBelow n)))
                                    [2..csetsz]
                samesUp = [TDucRelMapping relArgs ([n1,n2], LitFalse) | n1 <- [2..csetsz], n2 <- [2..csetsz], n1 >= n2]
                noneBelow :: Int -> MSOFormula
                noneBelow n = Prelude.foldl And LitTrue (Prelude.map Not (Prelude.drop n lics))
                noneAboveBetween :: Int -> Int -> MSOFormula
                noneAboveBetween highr lowr = Prelude.foldl And LitTrue (Prelude.map Not theLics)
                    where
                        theLics = Prelude.take ((lowr - highr)-1) (Prelude.drop highr lics)
        forPrec = downs ++ samesUp
            where
                downs = [lookingDown n1 n2 | n1 <- [1..csetsz], n2 <- [2..csetsz], n2 > n1]
                samesUp = [lookingUpOrEqual n1 n2 | n1 <- [1..csetsz], n2 <- [1..csetsz], n2 <= n1]
                lookingDown :: Int -> Int -> TDucRelMapping
                lookingDown n1 n2 = TDucRelMapping relArgs ([n1,n2], Or (Rel resName relArgs) (Equals a b))
                lookingUpOrEqual :: Int -> Int -> TDucRelMapping
                lookingUpOrEqual n1 n2 = TDucRelMapping relArgs ([n1,n2], Rel resName relArgs)

makeFaithfulMSOFormula :: SigRelation -> ([String],MSOFormula)
makeFaithfulMSOFormula (SigRelation rname ar) = (relArgs, fmla)
    where
        relArgs = ["v" ++ show i | i <- [1..ar]]
        fmla = Rel rname relArgs

makeFaithfulTDucRel :: Int -> SigRelation -> TDucRelation
--Faithful when arguments are from the first copy set, faithful for relations with an arity of 1, and False for
--  relations with an arity greater than one where any argument is not from the first copy set.
makeFaithfulTDucRel csetsz sigr@(SigRelation rname ar) = TDucRelation rname fmlas
    where
        (relArgs,fmla) = makeFaithfulMSOFormula sigr
        fmlas :: [TDucRelMapping]
        fmlas = if ar==1 then [TDucRelMapping relArgs ([mp1], fmla) | mp1 <- [1..csetsz]] else first:rest
            where
                first = TDucRelMapping relArgs (replicate ar 1, fmla) --all from 1st copy set
                rest = tail [TDucRelMapping relArgs (mp, LitFalse) | mp <- sequence (replicate ar [1..csetsz])]
