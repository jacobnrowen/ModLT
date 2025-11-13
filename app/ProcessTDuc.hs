module ProcessTDuc (getTransduction) where

import qualified Data.Set as S
import Data.List (delete, partition, sortBy)
import Data.Maybe (fromMaybe)
import TDucParser
import Recipes
import Types


getTransduction :: String -> Transduction
--Given raw text (presumably read from a transduction file),
--parse and process that text into a Transduction
getTransduction s = tduc
    where
        parsed = parseTDuc s
        (processed, recipes) = processParsedTDuc parsed
        postProc = applyRecipes recipes processed
        tduc = makeTDuc postProc


processParsedTDuc :: ParsedTDuc -> (ProcessedTDuc, [RecipeCall])
processParsedTDuc pTDuc = (ProcessedTDuc sig dom cset lics rels, recipes)
    where
        recipes = recDef pTDuc
        predsApplied = deSugarUserPreds pTDuc
        sig = makeSig predsApplied --Makes a signature if none provided
        dom = domDef predsApplied
        cset = csetDef predsApplied --Parser assumes copy set size of 1 if none provided
        lics = makeLicList predsApplied
        rels = makeTDucRels predsApplied


makeTDuc :: ProcessedTDuc -> Transduction
makeTDuc (ProcessedTDuc sig dom cset lics rels) = 
    if checkValidTransduction tduc then tduc
    else procError "Unspecified transduction processing error"
    where
        tduc = Transduction sig dom' cset lics' rels
        dom' = fromMaybe LitTrue dom --Domain is defaulted to true (strict checking already happened)
        lics' = case lics of
            []                  -> []
            Nothing:rest        -> ("(licV)", LitTrue) : makeRest rest
            (Just lic):rest     -> lic : makeRest rest
        makeRest [] = []
        makeRest (Nothing:rest) = ("(licV)", LitFalse) : makeRest rest
        makeRest ((Just lic):rest) = lic : makeRest rest



getFVar :: FormulaVar -> String
getFVar (ElemVar s) = s
getFVar (SetVar s)  = s

procError :: [Char] -> a
procError msg = error ("\nTransduction Processing Error:\n" ++ msg)





deSugarUserPreds :: ParsedTDuc -> ParsedTDuc
deSugarUserPreds (ParsedTDuc recs sig fdefs dom cset lics rels) = result
    where
        result = ParsedTDuc recs sig fdefs' dom' cset lics' rels'
        fdefs' = deSugarFormulas fdefs
        deSugar' = deSugarMSOBody fdefs' --Note that the formulas themselves had to be desugared first!
        dom' = case dom of
            Nothing -> Nothing
            Just fmla -> Just (deSugar' fmla)
        lics' = map deSugarLic lics
        rels' = map deSugarRel rels
        deSugarLic (LicDef lArg lMap lBody) = LicDef lArg lMap (deSugar' lBody)
        deSugarRel (RelMappingDef rN rA rM relBody) = RelMappingDef rN rA rM (deSugar' relBody)

makeSig :: ParsedTDuc -> Signature
--Do only after desugaring the user predicates!
makeSig (ParsedTDuc _ sig _ dom _ lics rels) = sig'
    where
        sig' = if sig /= [] then S.fromList sig else fromBodies `S.union` fromRelDefs
        fromBodies = foldr (S.union . getFormulaSignature) S.empty allFmlas
        fromRelDefs = S.fromList (map relDefToSigR rels)

        allFmlas = domFmla : (licFmlas ++ relFmlas)
        domFmla = fromMaybe LitFalse dom
        licFmlas = map licDefBody lics
        relFmlas = map relDefBody rels

        relDefToSigR :: RelMappingDef -> SigRelation
        relDefToSigR (RelMappingDef nm args _ _) = SigRelation nm (length args)


makeLicList :: ParsedTDuc -> [Maybe (String, MSOFormula)]
makeLicList (ParsedTDuc _ _ _ _ csetsz lics _ ) = result
    where
        result = makeList [] csetsz (sortBy cmpLic lics)
        cmpLic lic1 lic2 = compare (licDefMap lic2) (licDefMap lic1)
        makeList :: [Maybe (String, MSOFormula)] -> Int -> [LicDef] -> [Maybe (String, MSOFormula)]
        makeList acc 0 defs = case defs of
            [] -> acc
            _  -> procError "Duplicate, too many, or non-copy-set-matching licensing functions"
        makeList acc n [] = replicate n Nothing ++ acc
        makeList acc n lDefs@((LicDef arg mp body):rest) =
            if n /= mp then makeList (Nothing:acc) (n-1) lDefs
            else makeList (Just ("(licV)", normedBody) : acc) (n-1) rest
            where
                normedBody = replaceVars [(arg, "(licV)")] body

makeTDucRels :: ParsedTDuc -> S.Set TDucRelation
makeTDucRels (ParsedTDuc _ _ _ _ csetsz _ rels) = result
    where
        result = S.fromList (map makeTDucRelation (splitByName [] rels))
        makeTDucRelation :: [RelMappingDef] -> TDucRelation
        makeTDucRelation [] = undefined --Impossible state based on how splitByName works
        makeTDucRelation (r:rs) = TDucRelation (relDefName r) (map makeTDucRMap (r:rs))
            where
                makeTDucRMap (RelMappingDef rName rArgs rMap rBody) = case rMap of
                    [] -> if csetsz == 1 then TDucRelMapping rArgs (rep rArgs, rBody)
                            else procError ("Copy set information missing for mapping of relation: " ++ rName)
                    _ -> TDucRelMapping rArgs (rMap, rBody)
                rep :: [a] -> [Int]
                rep l = replicate (length l) 1
        splitByName :: [[RelMappingDef]] -> [RelMappingDef] -> [[RelMappingDef]]
        splitByName acc [] = acc
        splitByName acc (cur:rest) = splitByName ((cur:same):acc) diff
            where
                nm = relDefName cur
                (same,diff) = Data.List.partition (\r -> relDefName r == nm) rest






getFormulaSignature :: MSOFormula -> Signature
--Given an MSOFormula, determine the minimum Signature that formula is valid for
getFormulaSignature fmla = case fmla of
    Rel relName relParams -> S.singleton (SigRelation relName (length relParams))
    Not f -> getFormulaSignature f
    Exists _ f -> getFormulaSignature f
    Exists2 _ f -> getFormulaSignature f
    Forall _ f -> getFormulaSignature f
    Forall2 _ f -> getFormulaSignature f
    And f1 f2 -> getFormulaSignature f1 `S.union` getFormulaSignature f2
    Or f1 f2 -> getFormulaSignature f1 `S.union` getFormulaSignature f2
    Implies f1 f2 -> getFormulaSignature f1 `S.union` getFormulaSignature f2
    Iff f1 f2 -> getFormulaSignature f1 `S.union` getFormulaSignature f2
    _ -> S.empty


replaceVars :: [(String, String)] -> MSOFormula -> MSOFormula
replaceVars vars fmla = case fmla of
    Equals v1 v2 -> Equals (doVarMap vars v1) (doVarMap vars v2)
    ElemOf v1 v2 -> ElemOf (doVarMap vars v1) (doVarMap vars v2)
    Rel relName relParams -> Rel relName (map (doVarMap vars) relParams)
    Not f -> Not (replaceVars vars f)
    Exists a f -> Exists a (replaceVars vars f)
    Exists2 a f -> Exists2 a (replaceVars vars f)
    Forall a f -> Forall a (replaceVars vars f)
    Forall2 a f -> Forall2 a (replaceVars vars f)
    And f1 f2 -> And (replaceVars vars f1) (replaceVars vars f2)
    Or f1 f2 -> Or (replaceVars vars f1) (replaceVars vars f2)
    Implies f1 f2 -> Implies (replaceVars vars f1) (replaceVars vars f2)
    Iff f1 f2 -> Iff (replaceVars vars f1) (replaceVars vars f2)
    f -> f
    where
        doVarMap :: [(String, String)] -> String -> String
        doVarMap [] s = s
        doVarMap ((a,b):rest) s = if a == s then b else doVarMap rest s


deSugarMSOBody :: [FormulaDef] -> MSOFormula -> MSOFormula
--Replaces user-defined predicates in an MSOFormula with
--the proper formula from a list of formula definitions;
--make sure that the list of FormulaDef are themselves desugared first!
deSugarMSOBody fdefs fmla = case fmla of
    Rel relName relParams -> findFDef relName relParams fdefs
    Not f -> Not (deSugarMSOBody fdefs f)
    Exists a f -> Exists a (deSugarMSOBody fdefs f)
    Exists2 a f -> Exists2 a (deSugarMSOBody fdefs f)
    Forall a f -> Forall a (deSugarMSOBody fdefs f)
    Forall2 a f -> Forall2 a (deSugarMSOBody fdefs f)
    And f1 f2 -> And (deSugarMSOBody fdefs f1) (deSugarMSOBody fdefs f2)
    Or f1 f2 -> Or (deSugarMSOBody fdefs f1) (deSugarMSOBody fdefs f2)
    Implies f1 f2 -> Implies (deSugarMSOBody fdefs f1) (deSugarMSOBody fdefs f2)
    Iff f1 f2 -> Iff (deSugarMSOBody fdefs f1) (deSugarMSOBody fdefs f2)
    f -> f
    where
        findFDef :: String -> [String] -> [FormulaDef] -> MSOFormula
        findFDef relName relParams [] = Rel relName relParams
        findFDef relName relParams ((FormulaDef name args body):rest) =
            if relName /= name then findFDef relName relParams rest
            else replaceVars (zip (map getFVar args) relParams) body


deSugarFormulas :: [FormulaDef] -> [FormulaDef]
deSugarFormulas [] = []
deSugarFormulas allFormulas = result
    where
        result = case sorted of
            Nothing -> procError "Cyclic dependency or recursion found in user-defined predicates"
            Just fdefs -> deSugarAll [] fdefs
        names = S.fromList (map fmlaName allFormulas)
        sorted = sortFormulasByUse names [] allFormulas
        sortFormulasByUse :: S.Set String -> [FormulaDef] -> [FormulaDef] -> Maybe [FormulaDef]
        sortFormulasByUse _ acc [] = Just (reverse acc)
        sortFormulasByUse banned acc fmlas = case getOneFormula fmlas of
            Just fmla -> sortFormulasByUse (S.delete (fmlaName fmla) banned) (fmla:acc) (Data.List.delete fmla fmlas)
            Nothing -> Nothing
            where
            getOneFormula :: [FormulaDef] -> Maybe FormulaDef
            getOneFormula [] = Nothing
            getOneFormula (fmla:rest)
                |  selfLoop = Nothing  --No formula can recurse on itself; this will propagate an error
                |  noRely = Just fmla
                |  otherwise = getOneFormula rest
                where
                    noRely = S.disjoint banned rNames
                    rNames = S.map sigRname (getFormulaSignature (fmlaBody fmla))
                    selfLoop = fmlaName fmla `S.member` rNames
        deSugarAll :: [FormulaDef] -> [FormulaDef] -> [FormulaDef]
        deSugarAll acc [] = acc
        deSugarAll acc (cur:rest) = deSugarAll acc' rest
            where
                acc' = FormulaDef (fmlaName cur) (fmlaArgs cur) next:acc
                next = deSugarMSOBody acc (fmlaBody cur)

checkValidTransduction :: Transduction -> Bool
--DOES NOT CHECK THAT MSOFORMULAS ARE VALID (e.g. with regard to free variables)
checkValidTransduction (Transduction sig dom csize lics rels)
    | not validRelationMaps  = procError "At least one relation has some problem (error message work in progress)"
    | hasDuplicates = procError "Duplicate relation definition"
    | licsInconsistent = procError "The number of licensing functions does not match the copy set size"
    | relsInconsistent = procError "The number of relation definitions does not match the copy set size for at least one relation"
    | exhaustSig = procError "The number of relations in the signature does not match the number of relations defined"
    | not domMatchesSig = procError "The domain definition uses a relation that is not in the signature"
    | not licsMatchSig = procError "A licensing function uses a relation that is not in the signature"
    | not relMapsMatchSig = procError "At least one relation definition uses a relation that is not in the signature"
    | otherwise = True
    where
        validRelationMaps = all checkValidTDucRelation rels
        hasDuplicates = S.size rels /= S.size (S.map relationName rels)
        licsInconsistent = length lics /= csize
        relsInconsistent = any (/=csize) (S.map getTDucRelCSetSize rels)
        exhaustSig = S.size sig /= S.size rels
        matchesSig = (`S.isSubsetOf` sig) . getFormulaSignature
        domMatchesSig = matchesSig dom
        licsMatchSig = all (matchesSig . snd) lics
        relMapsMatchSig = all (all (matchesSig . snd . mapping)) (S.map formulas rels)
        getTDucRelCSetSize (TDucRelation _ fmlas) = maximum (map maximum setMappings)
            where
                setMappings = map (fst . mapping) fmlas

checkValidTDucRelation :: TDucRelation -> Bool
--DOES NOT CHECK THAT MSOFORMULAS ARE VALID (e.g. with regard to free variables)
checkValidTDucRelation (TDucRelation rName []) = procError ("No definition for relation: " ++ rName)
checkValidTDucRelation (TDucRelation rName fmlas@(headFmla:rest))
    | argsDontMatchMaps     = relErr "a mismatch in its number of arguments and its copy set mapping"
    | argsDontMatch         = relErr "a mismatch in its number of arguments"
    | mapsDontMatch         = relErr "a mismatch in its copy set mapping"
    | totalNumWrong         = relErr "too many or too few equation definitions"
    | hasDuplicates         = relErr "more than one definition for the same copy set mapping"
    | otherwise             = True
    where
        relErr s = procError ("Definition of relation " ++ rName ++ " has " ++ s)
        argsDontMatchMaps = headArgArity /= headMapArity
        argsDontMatch = any (\args -> getArgArity args /= headArgArity) rest
        mapsDontMatch = any (\relMap -> length (getSetMapping relMap) /= headMapArity) rest
        totalNumWrong = length setMappings /= topCSet ^ headArgArity
        hasDuplicates = S.size (S.fromList setMappings) /= length setMappings
        
        headArgArity = getArgArity headFmla
        headMapArity = length (getSetMapping headFmla)
        
        setMappings = map getSetMapping fmlas
        topCSet = maximum (map maximum setMappings)
        
        getSetMapping :: TDucRelMapping -> [Int]
        getSetMapping = fst . mapping
        
        getArgArity :: TDucRelMapping -> Int
        getArgArity = length . relArguments