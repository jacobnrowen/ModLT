module ProcessStructure (
    getStrucsFile,
    getResults
) where

import Types
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Data.List (find)
import StrucParser

getStrucsFile :: String -> ProcessedStrucsFile
getStrucsFile s = processParsedStrucs (parseStrucs s)

getResults :: ProcessedStrucsFile -> [Transduction] -> String
getResults (ProcessedStrucsFile sig alphaTbl strucs) tducs = result
    where
        result = if all ((==sig) . signature) tducs then outString
        else error "Error: structure file signature does not match transduction signature"
        outString = concatMap handleStruc strucs

        handleStruc :: (String, OrderedStructure) -> String
        handleStruc (name, struc) = "Results for " ++ name ++ ":\n" ++
                    showStruc (doTDucs struc tducs) ++ "\n\n"
        
        doTDucs :: OrderedStructure -> [Transduction] -> Either OrderedStructure String
        doTDucs struc [] = Left struc
        doTDucs struc (cur:rest) = case transduceStruc cur sig struc of
            Left struc' -> doTDucs struc' rest
            err -> err

        showStruc :: Either OrderedStructure String -> String
        showStruc (Right err) = err
        showStruc (Left (struc, [])) = strucRepr struc
        showStruc (Left (struc, orders)) = ordStr ++ "Structure:\n" ++ strucRepr struc
            where
                ordStr = case alphaTbl of
                    Nothing -> ""
                    Just tbl -> concatMap (handleToStr tbl) orders

                handleToStr tbl order = pref ++ str
                    where
                        pref = "String under order defined by relation " ++ orderRelName order ++ ":\n"
                        str = strucToString tbl (struc, order) ++ "\n"


processParsedStrucs :: ParsedStrucsFile -> ProcessedStrucsFile
processParsedStrucs (ParsedStrucsFile sig alphaTbl strucs) = ProcessedStrucsFile sig' alphaTbl strucs'
    where
        sig' = case sig of
            [] -> makeSig (map (relations . fst . snd) strucs')
            defs -> S.fromList defs
        strucs' = handleNames 1 (map getStruc strucs)

        makeSig :: [S.Set StrucRelation] -> Signature
        makeSig strucRs = S.map strucRtoSigR (foldr S.union S.empty strucRs)
            where
                strucRtoSigR (StrucRelation nm mems) = SigRelation nm (getArity mems)

        handleNames :: Int -> [(Maybe String, OrderedStructure)] -> [(String, OrderedStructure)]
        handleNames _ [] = []
        handleNames n ((Nothing,s):rest) = ("Structure "++ show n, s) : handleNames (n+1) rest
        handleNames n ((Just nm, s):rest) =  (nm, s) : handleNames (n+1) rest

        getStruc :: ParsedStruc -> (Maybe String, OrderedStructure)
        getStruc (ParsedStruc name orders sz rels) = (name, (struc, orders'))
            where
                (struc, orders') = case rels of
                    Left fullDef -> (handleFullDef sz fullDef, orders)
                    Right str -> case alphaTbl of
                        Just tbl -> stringToStruc tbl str
                        Nothing -> error
                            "Structure Parsing Error:\nStructure defined by string without AlphaMapTable"

        handleFullDef :: Maybe Int -> [(String, [RMember])] -> Structure
        handleFullDef sz rels = Structure sz' rels'
            where
                sz' = fromMaybe maxDomElem sz
                maxDomElem = getStrucSize allRMems
                allRMems = foldr S.union S.empty (S.map members rels')
                rels' = S.fromList (map makeStrucR rels)
                makeStrucR (nm, rmems) = StrucRelation nm (S.fromList rmems)

transduceStruc :: Transduction -> Signature -> OrderedStructure -> Either OrderedStructure String
--Assumes transduction signature and passed-in signature match each other
transduceStruc tduc strucSig (struc, orders) = result
    where
        result
            | strucError /= ""          = Right strucError
            | not matchesStrucFileSig   = Right "Error: structure does not match signature defined in Structure file"
            | not strucInDomain         = Left (struc, orders)
            | otherwise                 = Left (transduced, orders)
        strucError = getStructureError struc
        matchesStrucFileSig = strucMatchesSig struc strucSig
        strucInDomain = satisfied (domain tduc) [] struc
        transduced = applyTransduction tduc struc






stringToStruc :: AlphaMapTable -> String -> OrderedStructure
--Assumes string has spaces between each element
--If structure has exactly one element, makes placeholder starting and ending elements to prevent confusion
stringToStruc table str = (Structure numElem rels, orders)
    where
        symbls = if length (words str) /= 1 then words str else ["",str,""]
        numElem = length symbls
        unaries = mapFromAlpha table symbls
        succRel = buildSuccishRel "*" [1..numElem]
        precRel = buildPrecishRel "<" [1..numElem]
        rels = relations unaries `S.union` S.singleton succRel `S.union` S.singleton precRel
        orders = [StringOrder "*" SuccOrder [1,numElem], StringOrder "<" PrecOrder [1,numElem]]

mapFromAlpha :: AlphaMapTable -> [String] -> Structure
--Crucially, assumes all relations have an arity of 1!
mapFromAlpha table symbls = Structure numElem strucRs
    where
        numElem = length symbls
        strucRs = S.map makeStrucRs relNameSet
        relNameSet = S.foldl' S.union S.empty (S.fromList relList)
        relList = map findRule symbls
        numRelList = zip relList [1..numElem]
        genTable = reverse (mapRules table) --AlphaMapTables are most specific rules first, but we want most general here
        findRule :: String -> S.Set String
        findRule symbl = case filter (\(_,s) -> s == symbl) genTable of
            [] -> S.empty
            ((rl,_):_) -> rl
        makeStrucRs :: String -> StrucRelation
        makeStrucRs relName = StrucRelation relName mems
            where
                numList = filter (\(a,_) -> S.member relName a) numRelList
                mems = S.fromList (map ((:[]). snd) numList)

buildSuccishRel :: String -> [DomainElement] -> StrucRelation
--Given a list of domain elements, build a relation that connects them the way successor would
buildSuccishRel name domElems = StrucRelation name (getMems domElems)
    where
        getMems :: [DomainElement] -> S.Set RMember
        getMems [] = S.empty
        getMems [_] = S.empty
        getMems [a,b] = S.singleton [a,b]
        getMems (cur:(next:rest)) = S.singleton [cur,next] `S.union` getMems (next:rest)

buildPrecishRel :: String -> [DomainElement] -> StrucRelation
buildPrecishRel name domElems = StrucRelation name (getMems domElems)
    where
        getMems :: [DomainElement] -> S.Set RMember
        getMems [] = S.empty
        getMems [_] = S.empty
        getMems (cur:rest) = getCur `S.union` getMems rest
            where
                getCur = S.fromList (map (\n -> [cur,n]) rest)

alphaMap :: AlphaMapTable -> Structure -> [String]
--Has an extra empty string at index zero to make indexing by domain element convenient
alphaMap table (Structure numElem rels) = "":[findRule table n | n <- [1..numElem]]
    where
        findRule :: AlphaMapTable -> DomainElement -> String
        findRule (AlphaMapTable [] dflt) _ = dflt
        findRule (AlphaMapTable ((ruleRels,sym):rest) dflt) domElem =
            if ruleRels `S.isSubsetOf` relNames then sym else findRule (AlphaMapTable rest dflt) domElem
                where
                    relNames = (S.map strucRName . S.filter (any (elem domElem) . members)) rels

strucToString :: AlphaMapTable -> (Structure, StringOrder) -> String
strucToString table (struc, strOrd) = drop 1 result
    where
        result = foldl (\s1 s2 -> s1 ++ " " ++ s2) "" orderedStrs
        orderedStrs = map (syms!!) order
        syms = alphaMap table struc
        order = getOrdStrucDomElemString (struc, strOrd)

getOrdStrucDomElemString :: (Structure, StringOrder) -> [DomainElement]
getOrdStrucDomElemString (struc, StringOrder orderRel orderTyp orderInds) = result
    where
        result = case orderInds of
            [start,end] -> longPthBtwn orderRel orderTyp start end
            [] -> longestPath orderRel orderTyp
            _ -> orderInds --list of size three or greater
        longestPath "" CustomOrder = []
        longestPath "" SuccOrder = findLongestPath "*" struc
        longestPath "" PrecOrder = findLongestPath "<" struc
        longestPath relName _ = findLongestPath relName struc
        longPthBtwn "" CustomOrder s e = [s, e]
        longPthBtwn "" SuccOrder s e = longestPathBetween "*" struc s e
        longPthBtwn "" PrecOrder s e = longestPathBetween "<" struc s e
        longPthBtwn relName _ s e = longestPathBetween relName struc s e


longestPathBetween :: String -> Structure -> DomainElement -> DomainElement -> [DomainElement]
--Gives a path tied for longest path between the two elements, if one exists; otherwise [] 
longestPathBetween relName struc start end = if S.size result > 0 then S.elemAt 0 result else []
    where
        result = S.filter betw (getPaths relName struc)
        betw [] = False
        betw (hd:rest) = (hd == start) && (last rest == end)


findLongestPath :: String -> Structure -> [DomainElement]
--Gives a path tied for longest path, if one exists; otherwise []
findLongestPath relName struc = S.foldl findLongest [] (getPaths relName struc)
    where
        findLongest l1 l2 = if length l2 > length l1 then l2 else l1


getPaths :: String -> Structure -> S.Set [DomainElement]
--getPaths gets you the set of paths you can follow using a relation of
--arity 2, where paths are built by going from the first member of a relation to
--the second member, e.g. [[1,2], [2,3], [2,4], [4,1]] has paths:
--[[1,2,3], [1,2,4], [2,3], [2,4,1], [4,1,2,3]]
getPaths _ (Structure 0 _) = S.singleton []
getPaths _ (Structure 1 _) = S.singleton []
getPaths rname (Structure numElems rels) = if not hasSucc then S.singleton [] else paths
    where
        paths = S.fromList (concatMap (\d -> findPathsFrom d [] []) [1..numElems])

        findNext :: DomainElement -> [DomainElement]
        findNext cur = S.toList (S.map (!!1) (S.filter checkElem succMems))
            where
                checkElem mem = case mem of
                    [] -> False
                    fstElem:_ -> fstElem == cur

        findPathsFrom :: DomainElement -> [DomainElement] -> [DomainElement] -> [[DomainElement]]
        findPathsFrom d toHere excluding = if null nexts then [curAdded] else result
            where
                curAdded = toHere ++ [d]
                nexts = filter (`notElem` excluding) (findNext d)
                pathsFromNext = concatMap (\e -> findPathsFrom e [] (d:excluding)) nexts
                result = map (curAdded++) pathsFromNext

        (hasSucc, succMems) = case find (\rel -> strucRName rel == rname) rels of
                    Nothing -> (False, S.empty)
                    Just (StrucRelation _ mems) -> (all (\mem -> length mem == 2) mems, mems)




applyTransduction :: Transduction -> Structure -> Structure
--The resulting structure has domain elements equal to the size of the input structure times the copy set size, and
--   the elements are ennumerated accordingly
--ASSUMES TRANSDUCTION CAN APPLY
applyTransduction (Transduction _ _ _ lics tducRels) struc@(Structure numElem _) = resultStruc
    where
        resultStruc = Structure resultSize visRels
        resultSize = if S.size visRels == 0 then 0 else maximum (S.map (getStrucSize . members) visRels)
        visRels = S.map computeRel tducRels

        --Check license functions
        licensedDomElem :: [[DomainElement]]
        --licensedDomElem is the list of licensed domain elements in each copy set
        --It starts with an empty list so that index 1 is copy set 1 for convenience
        licensedDomElem = [] : map licenseHelper lics
            where
                licenseHelper :: (String, MSOFormula) -> [DomainElement]
                licenseHelper (vname, fmla) = filter (\i -> satisfied fmla [(vname,FO i)] struc) [1..numElem]

        computeElem :: DomainElement -> Int -> DomainElement
        computeElem inputDomElem cset = ((cset-1) * numElem) + inputDomElem

        computeRel :: TDucRelation -> StrucRelation
        computeRel (TDucRelation name relMaps) = StrucRelation name mems
            where
                memList = map computeRelMap relMaps
                mems = S.foldl' S.union S.empty (S.fromList memList)

        computeRelMap :: TDucRelMapping -> S.Set RMember
        computeRelMap (TDucRelMapping args (csetIds, fmla)) = result
            where
                result = S.fromList (testPermutations domElemLists [])

                domElemLists = map (licensedDomElem!!) csetIds

                convertDomElems :: [DomainElement] -> RMember
                convertDomElems domElems = zipWith computeElem domElems csetIds

                testStep :: [DomainElement] -> Bool
                testStep domElems = satisfied fmla (zip args (map FO domElems)) struc

                testPermutations :: [[DomainElement]] -> [DomainElement] -> [RMember]
                testPermutations [] _ = []
                testPermutations ([]:_) _ = []
                testPermutations [domElem:restInSet] curElems = testPermutations [restInSet] curElems ++
                    ([convertDomElems (curElems++[domElem]) | testStep (curElems++[domElem])])

                testPermutations ((domElem:restInSet):otherSets) curElems =
                    testPermutations otherSets (domElem:curElems) ++ testPermutations (restInSet:otherSets) curElems


strucRepr :: Structure -> String
strucRepr (Structure 0 _) = "Size: 0"
strucRepr (Structure numElem rels) = foldl (\cur nxt -> cur ++ showStrucRs nxt) header byArity
    where
        header = "Size: " ++ show numElem
        getArOfStrucR strucR = getArity (members strucR)
        highestArity = S.foldl' (\cur nxt -> max cur (getArOfStrucR nxt)) (-1) rels
        justar n = S.filter (\r -> getArOfStrucR r == n) rels
        byArity = [justar n | n <- [1..highestArity]]
        showStrucRs = S.foldl' (\cur nxt -> cur ++ "\n" ++ strucRRepr nxt) ""
        strucRRepr :: StrucRelation -> String
        strucRRepr (StrucRelation name mems) = name ++ "\n" ++ show (S.toList mems)



satisfied :: MSOFormula -> VarContext -> Structure -> Bool
--Check if a particular MSOFormula is true for the particular variable values given
--Note that, because of the way the recursion is being done and the way lookup works,
--lookiing up a variable will always give the most local value bound to that variable name
satisfied LitTrue _ _ = True
satisfied LitFalse _ _ = False

satisfied (Not formula) args struc = not (satisfied formula args struc)
satisfied (And f1 f2) args struc = satisfied f1 args struc && satisfied f2 args struc
satisfied (Or f1 f2) args struc = satisfied f1 args struc || satisfied f2 args struc
satisfied (Implies f1 f2) args struc = not (satisfied f1 args struc) || satisfied f2 args struc
satisfied (Iff f1 f2) args struc = satisfied f1 args struc == satisfied f2 args struc

satisfied (Equals v1 v2) args _ = case (lookup v1 args, lookup v2 args) of
    (Just (FO n1), Just (FO n2))  -> n1 == n2
    _                             -> error ("Variables passed to == are second order or don't exist:" ++ show v1 ++ ", " ++ show v2)

satisfied (Rel relName relParams) args struc = queryStructure relName relArgs struc
    where
        relArgs = map lookupFO relParams
        lookupFO varname = case lookup varname args of
            Just (FO n)     -> n
            Just (MSO _)    -> error "Trying to pass monadic set variable to relation"
            Nothing         -> error ("Unbound variable: " ++ show varname)

satisfied (ElemOf foVar setVar) args _ = S.member foVal setVal
    where
        foVal = case lookup foVar args of
            Just (FO f)     -> f
            Just (MSO _)    -> error ("Trying to check if monadic set variable " ++ show foVar ++ " is element of set")
            Nothing         -> error ("Unbound variable: " ++ show foVar)
        setVal = case lookup setVar args of
            Just (FO _)     -> error ("Trying to get element of first order variable: " ++ show setVar)
            Just (MSO m)    -> m
            Nothing         -> error ("Unbound variable: " ++ show setVar)


satisfied quantifier args struc = case quantifier of
    Exists  var formula -> satisfyQuantifier var formula maxElement True
    Forall  var formula -> satisfyQuantifier var formula maxElement False
    Exists2 var formula -> satisfyMQuantifier var formula maxSet True
    Forall2 var formula -> satisfyMQuantifier var formula maxSet False
    where
        maxElement = numElements struc
        powSet = S.powerSet (S.fromList [0..maxElement])
        maxSet = S.size powSet - 1

        satisfyQuantifier :: String -> MSOFormula -> DomainElement -> Bool -> Bool
        --Try domain elements until stopOn is reached or domain elements run out
        --Remember that domain elements are one-indexed!
        satisfyQuantifier var formula cur_element stopOn
            | cur_element == 1  = takeStep == stopOn
            | takeStep == stopOn    = stopOn
            | otherwise         = recurse
            where
                takeStep    = satisfied formula ((var, FO cur_element):args) struc
                recurse = satisfyQuantifier var formula (cur_element-1) stopOn

        satisfyMQuantifier :: String -> MSOFormula -> Int -> Bool -> Bool
        --Try each possible set of domain elements until stopOn is reached or possible sets run out
        satisfyMQuantifier var formula cur_set stopOn
            | cur_set == 0      = takeStep == stopOn
            | takeStep == stopOn    = stopOn
            | otherwise         = recurse
            where
                takeStep    = satisfied formula ((var, MSO (S.elemAt cur_set powSet)):args) struc
                recurse = satisfyMQuantifier var formula (cur_set-1) stopOn


--queryStructure assumes that the relation is syntactically valid for the structure
queryStructure :: String -> RMember -> Structure -> Bool
queryStructure rname rmem (Structure _ rels) = any procRel rels
  where
    --For each relation in the structure, check if it has the queried name, 
    --and then check if it includes the queried member
    procRel (StrucRelation name mems) = rname == name && S.member rmem mems


getArity :: S.Set [DomainElement] -> Int
getArity mems = case S.toList mems of
    [] -> 0 --This usually shouldn't happen
    (m:_) -> length m




getStructureError :: Structure -> String
getStructureError (Structure numElem rels) = strucError
    where
        strucError
            | duplicateRelations        = "Error: at least one duplicate relation definition"
            | S.size strucRErrors > 0     = S.elemAt 0 strucRErrors
            | otherwise                 = ""
        duplicateRelations = S.size (S.map strucRName rels) /= S.size rels
        strucRErrors = S.filter (/= "") (S.map getStrucRError rels)

        getStrucRError (StrucRelation nm mems) = strucRError
            where
                strucRError
                    | unequalArity = "Error: members of relation " ++ nm ++ " do not all have equal arity"
                    | invalidElems = "Error: domain element out of size range in relation " ++ nm
                    | otherwise    = ""
                unequalArity  = any ((/= getArity mems) . length) mems
                invalidElems  = getStrucSize mems > numElem


strucMatchesSig :: Structure -> Signature -> Bool
--Check whether a structure matches a particular signature
strucMatchesSig (Structure _ rels) sig = all (\strucR -> any (strucRmatchesSigR strucR) sig) rels
    where
        strucRmatchesSigR :: StrucRelation -> SigRelation -> Bool
        strucRmatchesSigR (StrucRelation strucN m) (SigRelation sigN ar) = case S.toList m of
            [] -> True  --if the relation contains nothing, it vacuously matches the signature
            (s1:_) -> strucN == sigN && length s1 == ar  --the name and arity must match

getStrucSize :: S.Set RMember -> Int
getStrucSize mems = if S.size mems /= 0 then maximum (S.map maximum mems) else 0