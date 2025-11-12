module Types (
--Transductions and Their Component Types--
    Transduction(..),
    SigRelation(..),
    Signature,
    MSOFormula(..),
    TDucRelMapping(..),
    TDucRelation(..),
--Structures and Related Types--
    DomainElement,
    StrucRelation(..),
    Structure(..),
    RMember,
    VarValue(..),
    VarContext,
    StringOrderType(..),
    StringOrder(..),
    OrderedStructure,
--Intermediate Types for Parsing--
    ParsedTDuc(..),
    ProcessedTDuc(..),
    RecipeCall(..),
    Recipe,
    FormulaVar(..),
    FormulaDef(..),
    LicDef(..),
    RelMappingDef(..),
    ParsedStrucsFile(..),
    ParsedStruc(..),
    ProcessedStrucsFile(..),
--Types for Other Utilities--
    AlphaMapRule,
    AlphaMapTable(..),

--Type Validity Checking Functions
    isValidTDucRelation
) where
import Data.Set


-------------------------------------------------------------------------------
--------------------Transductions and Their Component Types--------------------
-------------------------------------------------------------------------------

data Transduction = Transduction {
    signature :: Signature,
    domain :: MSOFormula,
    cSetSize :: Int,
    licensors :: [(String, MSOFormula)],
    relationMaps :: Set TDucRelation
} deriving (Show)

data SigRelation = SigRelation {
        sigRname :: String,
        arity :: Int
} deriving (Show, Eq, Ord)

type Signature = Set SigRelation


data MSOFormula =
    LitTrue
  | LitFalse
  | Equals String String
  | Not MSOFormula
  | And MSOFormula MSOFormula
  | Or MSOFormula MSOFormula
  | Implies MSOFormula MSOFormula
  | Iff MSOFormula MSOFormula
  | Exists String MSOFormula
  | Exists2 String MSOFormula
  | Forall String MSOFormula
  | Forall2 String MSOFormula
  | ElemOf String String
  | Rel String [String]
  deriving (Show, Eq)


--The Transduction Relation Mapping is responsible for storing the MSO Formula defining a relation between copy sets
data TDucRelMapping = TDucRelMapping {
    relArguments :: [String],
    mapping :: ([Int], MSOFormula)
} deriving (Show, Eq)
instance Ord TDucRelMapping where
    --This is just to make sure Set operations work on expected on TDucRelMappings
    (<=) a b = csets a <= csets b
        where
            csets :: TDucRelMapping -> [Int]
            csets (TDucRelMapping _ (sets, _)) = sets

data TDucRelation = TDucRelation {
    relationName :: String,
    formulas :: [TDucRelMapping]
} deriving (Show, Eq)
instance Ord TDucRelation where
    --This is just to make sure Set operations work on expected on TDucRelations
    (<=) a b = relationName a <= relationName b


-------------------------------------------------------------------------------
-------------------------Structures and Related Types--------------------------
-------------------------------------------------------------------------------

type DomainElement = Int

--A structure is a set of natural-numbered elements (represented here by aliasing Int)
--with a set of relations over those elements

--These relations have names and a set of their members
data StrucRelation = StrucRelation
        {
        strucRName :: String,
        members :: Set RMember
        } deriving (Show, Eq, Ord)

data Structure = Structure
    {
    numElements :: Int,
    relations :: Set StrucRelation
    } deriving (Show, Eq, Ord)

type RMember = [DomainElement]
data VarValue = FO DomainElement | MSO (Set DomainElement)
type VarContext = [(String, VarValue)]

data StringOrderType = SuccOrder | PrecOrder | CustomOrder deriving (Enum, Eq, Show, Ord)

--StringOrder objects are very particular in their proper use.
--orderType has three well-defined possibilities:
--  SuccOrder, which is meant for successor-like ordering
--  PrecOrder, which is meant for precedence-like ordering
--  CustomOrder, which has no corresponding relation
--If the orderType is SuccOrder or PrecOrder, then:
--  If the orderRelName is "", it will be assumed to be "*" or "<" respectively
--  If the orderIndices are [], they will be assumed to be the longest contiguous sequence of
--      DomainElements buildable under the orderRelName and type
--  If the orderIndices are a list of size 2, the 2 indices will be assumed to be the start and end indices,
--      and the indices between will be inferred in the appropriate style
--  If the orderIndices are anything else, they will supercede all else and all assumptions and will be
--      treated as simply being the canonical order of the domain elements, no matter what
--If the orderType is CustomOrder, then orderIndices will be used as the canonical order, disregarding all else
--  as in the last case for SuccOrder or PrecOrder
data StringOrder = StringOrder {
    orderRelName :: String,
    orderType :: StringOrderType,
    orderIndices :: [DomainElement]
} deriving (Show, Eq, Ord)

type OrderedStructure = (Structure, [StringOrder])


-------------------------------------------------------------------------------
------------------------Intermediate Types for Parsing-------------------------
-------------------------------------------------------------------------------

--ParsedTDuc is the data structure that comes straight out of the parser
data ParsedTDuc = ParsedTDuc {
    recDef :: [RecipeCall],
    sigDef :: [SigRelation],
    fmlasDef :: [FormulaDef],
    domDef :: Maybe MSOFormula,
    csetDef :: Int,
    licsDef :: [LicDef],
    relsDef :: [RelMappingDef]
} deriving (Show)

--ProcessedTDUc is the data structure after the parser output has been processed,
--such that, for example, the user-defined predicates have been applied where appropriate,
--but before any recipes have been applied and semantic validity checks have been done
data ProcessedTDuc = ProcessedTDuc {
    sigProc :: Signature,
    domProc :: Maybe MSOFormula,
    csetProc :: Int,
    licsProc :: [Maybe (String, MSOFormula)],
    relsProc :: Set TDucRelation
}

data RecipeCall = RecipeCall {
    recipeName :: String,
    recipeArgs :: [String]
} deriving (Show)

type Recipe = ([String] -> ProcessedTDuc -> ProcessedTDuc)

--For now, the difference between ElemVar and SetVar isn't used,
--as the relevant checking happens "at runtime" so to speak,
--without access to this information. Some day, it would be good to
--check this properly, but for now just the underlying String is used.
data FormulaVar = ElemVar String | SetVar String
    deriving (Show, Eq)


data FormulaDef = FormulaDef {
    fmlaName :: String,
    fmlaArgs :: [FormulaVar],
    fmlaBody :: MSOFormula
}  deriving (Show, Eq)

data LicDef = LicDef {
    licDefArg  :: String,
    licDefMap  :: Int,
    licDefBody :: MSOFormula
}  deriving (Show)

data RelMappingDef = RelMappingDef {
    relDefName :: String,
    relDefArgs :: [String],
    relDefMap  :: [Int],
    relDefBody :: MSOFormula
}  deriving (Show)

data ParsedStrucsFile = ParsedStrucsFile {
    strucSigDef :: [SigRelation],
    alphaMapDef :: Maybe AlphaMapTable,
    parsedStrucs :: [ParsedStruc]
}  deriving (Show)

data ProcessedStrucsFile = ProcessedStrucsFile {
    strucsSigProc :: Signature,
    alphaMapProc :: Maybe AlphaMapTable,
    strucsProc :: [(String, OrderedStructure)]
}

data ParsedStruc = ParsedStruc {
    strucNameDef :: Maybe String,
    strucOrderDef :: [StringOrder],
    strucSizeDef :: Maybe Int,
    strucRelsDef :: Either [(String, [RMember])] String
}  deriving (Show)


-------------------------------------------------------------------------------
---------------------------Types for Other Utilities---------------------------
-------------------------------------------------------------------------------

type AlphaMapRule = (Set String, String)
--AlphaMapTables allow for the easy printing out of representations of structures that use
--a feature system or similar to describe individual characters. Each "row" of the table
--is a list of relations, followed by the symbol that should be used if a domain element
--is in each of these relations. The tables are ordered, so the first such rule that a
--domain element matches is the rule that will be used to represent that domain element.
--Therefore, it is recommended that the rules are placed in increasing order of generality.
--To prevent catastrophic errors, all tables MUST come with a default symbol to use when no rule applies.
data AlphaMapTable = AlphaMapTable {
    mapRules :: [AlphaMapRule],
    defaultSymbol :: String
} deriving Show



-------------------------------------------------------------------------------
-----------------------Type Validity Checking Functions------------------------
-------------------------------------------------------------------------------

isValidTDucRelation :: TDucRelation -> Bool
--DOES NOT CHECK THAT MSOFORMULAS ARE VALID (e.g. with regard to free variables)
isValidTDucRelation (TDucRelation _ relMaps) = case relMaps of
    [] -> False
    fmlas@(headFmla:rest) -> consistentArity && consistentCSetSize
        where
            consistentArity = headArgArity == headMapArity && argsMatch && mapsMatch
            consistentCSetSize = totalNumCorrect && noDuplicates

            headArgArity = getArgArity headFmla
            headMapArity = length (getSetMapping headFmla)
            argsMatch = all (\args -> getArgArity args == headArgArity) rest
            mapsMatch = all (\relMap -> length (getSetMapping relMap) == headMapArity) rest

            totalNumCorrect = length setMappings == topCSet ^ headArgArity
            noDuplicates = size (fromList setMappings) == length setMappings
            
            setMappings = Prelude.map getSetMapping fmlas
            topCSet = maximum (Prelude.map maximum setMappings)
            
            getSetMapping :: TDucRelMapping -> [Int]
            getSetMapping = fst . mapping
            
            getArgArity :: TDucRelMapping -> Int
            getArgArity = length . relArguments

            

            

            

            

            