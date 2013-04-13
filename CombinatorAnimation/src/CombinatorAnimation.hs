{-# LANGUAGE ScopedTypeVariables, TypeFamilies, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------------
--
-- Module      :  CombinatorAnimation
-- Copyright   :  (c) 2012 Jürgen Nicklisch-Franken
-- License     :  AllRightsReserved
--
-- | Combinatory logic animation.
--
-----------------------------------------------------------------------------

module CombinatorAnimation where

import Combinators
import ConeCanvas.OntoTransforms
import ConeCanvas.OntoModel

import Graphics.UI.Gtk
import Data.Maybe (catMaybes)
import Data.IORef


data OntoCigolState = OntoCigolState {
--    basis :: BasisSelection
    }

data EditTerm v =
    TermIKS (Term IKS v)
    | TermBCKW (Term BCKW v)
    deriving (Eq, Show)

showTerm :: Variable v => EditTerm v -> String
showTerm (TermIKS i) = pprint i
showTerm (TermBCKW i) = pprint i

instance Variable v => OntoEntry (EditTerm v) where
    type UserState (EditTerm v) = ()
    omeLabel (TermIKS x)  = pprint x
    omeLabel (TermBCKW x)  = pprint x
    omeIcon  (TermIKS(Var _)) = Just "var"
    omeIcon  (TermBCKW(Var _)) = Just "var"
    omeIcon  (TermIKS (Const c)) = Just (combName c)
    omeIcon  (TermBCKW (Const c)) = Just (combName c)
    omeIcon  _ = Nothing
    omeIsLeaf (TermIKS(_:@_)) = False
    omeIsLeaf (TermBCKW(_:@_)) = False
    omeIsLeaf _ = True
        -- May the entry have child nodes?
    omeActions _ = []

toOntoModel :: Variable v => EditTerm v ->  OntoNode (EditTerm v)
toOntoModel term = case term of
                    TermIKS t -> toOntoModel' t
                    TermBCKW t -> toOntoModel'' t
  where
    toOntoModel' t@(Const _c) =  constrOntoNode' (TermIKS t) []
    toOntoModel' t@(Var _v)   =  constrOntoNode' (TermIKS t) []
    toOntoModel' t@(_t1:@_t2) =  constrOntoNode' (TermIKS t)
                                            (map (toOntoModel . TermIKS) (spine (_t1 :@ _t2)))
    toOntoModel'' t@(Const _c) =  constrOntoNode' (TermBCKW t) []
    toOntoModel'' t@(Var _v)   =  constrOntoNode' (TermBCKW t) []
    toOntoModel'' t@(_t1:@_t2) =  constrOntoNode' (TermBCKW t)
                                            (map (toOntoModel . TermBCKW) (spine (_t1 :@ _t2)))

toOntoHeadSepModel :: Variable v => EditTerm v ->  OntoNode (EditTerm v)
toOntoHeadSepModel term = case term of
                    TermIKS t -> toOntoModel' TermIKS t
                    TermBCKW t -> toOntoModel' TermBCKW t
  where
    toOntoModel' constr t@(Const _c) =  constrOntoNode' (constr t) []
    toOntoModel' constr t@(Var _v)   =  constrOntoNode' (constr t) []
    toOntoModel' constr t@(t1:@t2) = constrOntoNode' (constr t)
                                        (if isApp t1
                                            then (toOntoModel . constr) t1 : [(toOntoModel . constr) t2]
                                            else map (toOntoModel . constr) (spine (t1:@t2)))



toTerm :: Variable v => OntoNode (EditTerm v) -> EditTerm v
toTerm OntoNode{omEntry = OMEntry term} = term
toTerm _ = error "CombinatorAnimation>>toTerm: Called for Neutral element"


setComb :: OntoSelection (EditTerm VarString) -> Entry -> OntoInterface (EditTerm VarString) -> IO ()
setComb comb entry interface = do
        omSetModel interface comb []
        entrySetText entry (showTerm (toTerm (selModelFromRoot comb)))

standardIKS, standardBCKW :: OntoSelection (EditTerm VarString)
standardIKS = standardComb TermIKS  "S S K (S (K (S S (S (S S K)))) K) I"
standardBCKW = standardComb TermBCKW "B x y z"

standardComb :: (Basis b v) => (Term b v -> EditTerm v) -> String -> OntoSelection (EditTerm v)
standardComb constr string =
    let term = parse string
        model = toOntoModel (constr term)
    in selFromModel' model


runIt :: forall v. Variable v => Bool -> IORef OntoCigolState -> OntoInterface (EditTerm v) -> Entry ->
    CheckButton -> IO ()
runIt False _stateRef interface _entry _button = omAnimateFinishedCallback interface (return ())
runIt True _stateRef interface entry button = do
    (sel,_rel) <- omGetModel interface
    let term = case sel of
                    OSCurrent pos -> toTerm (ontoNodeFromRoot pos)
                    OSParent pos -> toTerm (ontoNodeFromRoot pos)
    case term of
        TermIKS term -> animateTerm term TermIKS
        TermBCKW term -> animateTerm term TermBCKW
  where
    animateTerm :: forall basis. TransformableBasis basis v => Term basis v -> (Term basis v -> EditTerm v) -> IO ()
    animateTerm term constr =
        let zipper = constrZipper term
        in case applyStrategy normalOrderStrategy zipper of
            Just (zipper',(comb,args)) -> do
                let newTerm = zipTerm (applyCombinator (zipper',(comb,args)))
                entrySetText entry (pprint newTerm)
                let selection = selFromModel' (toOntoModel (constr newTerm))
                    transformations = transDescr comb (zipperGetPath zipper') args selection
                omTransform interface transformations
                omAnimateFinishedCallback interface (animateTerm newTerm constr)
            Nothing -> do
                omAnimateFinishedCallback interface (return ())
                toggleButtonSetActive button False



stepIt :: forall v. Variable v => IORef OntoCigolState -> OntoInterface (EditTerm v) -> Entry -> IO ()
stepIt _stateRef interface entry = do
    (sel,_rel) <- omGetModel interface
    let term = case sel of
                    OSCurrent pos -> toTerm (ontoNodeFromRoot pos)
                    OSParent pos -> toTerm (ontoNodeFromRoot pos)
    case term of
        TermIKS term -> animateTerm term TermIKS
        TermBCKW term -> animateTerm term TermBCKW
  where
    animateTerm :: forall basis. TransformableBasis basis v => Term basis v -> (Term basis v -> EditTerm v)  -> IO ()
    animateTerm term constr =
        let zipper = constrZipper term
        in case applyStrategy normalOrderStrategy zipper of
            Just (zipper',(comb,args)) -> do
                let newTerm = zipTerm (applyCombinator (zipper',(comb,args)))
                entrySetText entry (pprint newTerm)
                let selection = selFromModel' (toOntoModel (constr newTerm))
                    transformations = transDescr comb (zipperGetPath zipper') args selection
                omTransform interface transformations
            Nothing -> return ()

calcChangeHead :: OntoPath -> Int -> Int -> [(OntoPath, Maybe OntoPath)]
calcChangeHead path spl size = changeHead ++ changeRest
  where
    changeHead =  if spl == 1
                    then []
                    else prepends2 (path ++ [0]) path
                                (map (\i -> (i,i))
                                    [0..spl-1])
    changeRest =  if spl == 1
                    then []
                    else prepends path
                            (map (\i -> (i-(spl-1),i))
                                [spl..size-1])



-- | Any combinatory basis which implements this is gets animatable in an ontoPanel
class Basis basis v => TransformableBasis basis v where
    transDescr :: Combinator basis v -> OntoPath -> [Term basis v] -> OntoSelection (EditTerm v)
                    -> [Transformation (EditTerm v)]

-- ^ Return an animation descrition for a primitive combinator
-- The first argument is the combinator.
-- The second argument is the path to the combinator, without the last 0.
-- The third argument are the possible arguments to the combinator.
-- The fourth argument is the OntoPos after the transformation
-- An exception is raised, when not enough args are provided

instance Variable v => TransformableBasis IKS v where
        -- I Combinator I x = x
    transDescr c path a p | c == iIKS && not (null a) =
        let n = length a
            spl = spineLength (head a)
            newSize = spl + n - 1
            changes = (changePaths changeFuse) . (changePaths changeList)
            changeList = removeHead : changeHead : changeRest
            removeHead = (path ++ [0],Nothing)
            changeHead = (path ++ [1],Just (path ++ [0]))
            changeRest = prepends path
                            (map (\i -> (i,normalizePos  (i - 1) n))
                                [2..n])
            changeFuse = calcChangeHead path spl newSize
        in  map (\(t,c) -> Transformation t p c) $
                catMaybes [Just ([TPTransOp (TOFade (Just True)) (TPAim (path ++ [0])),
                                  TPTransOp (TOTurn True (0,newSize) TDAntiClockwise)
                                        (TPAim (path ++ [1]))]
                                    ++  slide path 2 (n+1) newSize True, changes),
                                    fuseHead (TermIKS (head a)) path newSize]

        -- K Combinator  K x y = x
                            | c == kIKS && length a >= 2 =
        let n = length a
            spl = spineLength (head a)
            newSize = spl + n - 2
            changeList = removeHead : removeY : changeX : changeRest
            removeHead = (path ++ [0],Nothing)
            changeX = (path ++ [1], Just (path ++ [0]))
            removeY = (path ++ [2], Nothing)
            changeRest = prepends path
                            (map (\i -> (i,normalizePos (i - 2) (n-1)))
                                [3..n])

        in  map (\(t,c) -> Transformation t p c) $
                catMaybes [Just ([TPTransOp (TOSizeChange (newSize,True)) (TPAim path),
                                  TPTransOp (TOFade (Just True)) (TPAim (path ++ [0])),
                                  TPTransOp (TOTurn True (0,newSize) TDAntiClockwise) (TPAim (path ++ [1])),
                                  TPTransOp (TOFade (Just True)) (TPAim (path ++ [2]))]
                                    ++ slide path 3 (n+1) newSize True, changePaths changeList),
                                    fuseHead (TermIKS (head a)) path newSize]

        -- S Combinator  S x y z = x z (y z)
                            | c == sIKS && length a >= 3 =
        let n          = length a
            spl        = spineLength (head a)
            spl1       = spineLength (a !! 1)
            newSize    = spl + n - 1
            changeList = removeHead : changedX : changedY : changedZ : changeRest
            removeHead = (path ++ [0],Nothing)
            changedX   = (path ++ [1],Just (path ++ [0]))
            changedY   = (path ++ [2],Just (path ++ [2,0]))
            changedZ   = (path ++ [3],Just (path ++ [1]))
            changeRest = prepends path (map (\i -> (i,normalizePos (i - 1) n)) [4..n])
            introZ     = OntoRelation (path ++ [1]) (path ++ [2,1]) True
        in  map (\(t,c) -> Transformation t p c) $
            catMaybes [Just ([TPTransOp (TOFade (Just True)) (TPAim (path ++ [0])),
                                TPTransOp (TOTurn True (0,newSize) TDAntiClockwise) (TPAim (path ++ [1])),
                                TPTransOp (TOFade (Just True)) (TPAim (path ++ [2])),
                                TPTransOp (TOTurn True (spl,newSize) TDAntiClockwise) (TPAim (path ++ [3])),
                                TPLift False (IntroDef path (spl + 1,newSize)
                                    (toOntoHeadSepModel (TermIKS ((a !! 1) :@ (a !! 2))))
                                    (rearrangeForSize [] 2 newSize (n + 1) False))]
                                    ++ slide path 4 (n+1) newSize True,
                                        (\r -> introZ : changePaths changeList r)),
                                    together (fuseHead (TermIKS (head a)) path newSize)
                                             (together (fuseHead (TermIKS (a !! 1)) (path ++ [spl +1]) (spl1 + 1))
                                                (Just (slide (path ++ [spl + 1]) 1  (spl1 + 1) 2 False, id)))]
                            | otherwise =
        error $ "transDescr: unsufficient arity " ++ show c ++ " " ++ show (length a)

instance Variable v => TransformableBasis BCKW v where
    transDescr c path a s   | c == bBCKW && length a >= 3 =
        -- B x y z = x (y z)
        let n = length a
            spl = spineLength (head a)
            spl1 = spineLength (a !! 1)
            newSize = spl + n - 2
        in  map (\(t,c) -> Transformation t s c) $
                catMaybes [Just ([TPTransOp (TOFade (Just True)) (TPAim (path ++ [0])),
                                  TPTransOp (TOTurn True (0,newSize) TDAntiClockwise) (TPAim (path ++ [1])),
                                  TPTransOp (TOFade Nothing) (TPAim (path ++ [2])),
                                  TPTransOp (TOFade Nothing) (TPAim (path ++ [3])),
                                  TPLift False (IntroDef path (spl,newSize{-hang here-})
                                    (toOntoHeadSepModel (TermBCKW ((a !! 1) :@ (a !! 2))))
                                    (rearrangeForSize [] 2 newSize{-below-} (n + 1){-above-} False))
                                  ]
                                    ++ slide path 4 (n+1) newSize True, id),
                                    together (fuseHead (TermBCKW (head a)) path newSize)
                                        (together (fuseHead (TermBCKW (a !! 1)) (path ++ [spl]) (spl1 + 1))
                                            (Just (slide (path ++ [spl]) 1  (spl1 + 1) 2 False, id)))]

                            | c == cBCKW && length a >= 3 =
        -- C x y z = x z y
        let n = length a
            spl = spineLength (head a)
            newSize = spl + n - 1
        in  map (\(t,c) -> Transformation t s c) $
                catMaybes [Just ([TPTransOp (TOFade (Just True)) (TPAim (path ++ [0])),
                                  TPTransOp (TOTurn True (0,n) TDAntiClockwise) (TPAim (path ++ [1])),
                                  TPTransOp (TOTurn True (spl+1,newSize) TDClockwise) (TPAim (path ++ [2])),
                                  TPTransOp (TOTurn True (spl,newSize) TDAntiClockwise) (TPAim (path ++ [3]))]
                                    ++ slide path 4 (n+1) newSize True, id),
                                    fuseHead (TermBCKW (head a)) path newSize]

                            | c == kBCKW && length a >= 2 =
        -- K x y = x
        let n = length a
            spl = spineLength (head a)
            newSize = spl + n - 2
        in  map (\(t,c) -> Transformation t s c) $
                catMaybes [Just ([TPTransOp (TOFade (Just True))(TPAim (path ++ [0])),
                                  TPTransOp (TOTurn True (0,newSize) TDAntiClockwise) (TPAim (path ++ [0])),
                                  TPTransOp (TOFade (Just True)) (TPAim (path ++ [0]))]
                                    ++ slide path 3 (n+1) newSize True, id),
                                    fuseHead (TermBCKW (head a)) path newSize]

                            | c == wBCKW && length a >= 2 =
        -- W x y = x y y
        let n = length a
            spl = spineLength (head a)
            newSize = spl + n
        in  map (\(t,c) -> Transformation t s c) $
                catMaybes [Just ([TPTransOp (TOFade (Just True)) (TPAim (path ++ [0])),
                                  TPTransOp (TOTurn True (0,newSize) TDAntiClockwise)(TPAim (path ++ [1])),
                                  TPTransOp (TOTurn True (1,newSize) TDAntiClockwise)(TPAim (path ++ [2])),
                                  TPIntro (IntroDef path (2,newSize) (toOntoModel (TermBCKW (a !! 1))) [])]
                                  ++ slide path 3 (n+1) newSize True, id),
                                    fuseHead (TermBCKW (head a)) path newSize]

                            | otherwise =
        error $ "transDescr: unsufficient arity " ++ show c ++ " " ++ show (length a)


-- | Makes an animation by adding the spine of the head tree into the main tree
-- Size is the size of the spine of the resulting combinator
fuseHead :: Variable v => EditTerm v -> [Int] -> Int ->
                Maybe ([TransformationPrim (EditTerm v)],[OntoRelation] -> [OntoRelation])
fuseHead et path size = case et of
                                (TermIKS t@(_ :@ _)) -> Just (fuseHead' t,id)
                                (TermBCKW t@(_ :@ _)) -> Just (fuseHead'' t,id)
                                _ -> Nothing
  where
    fuseHead' t =
        let sp = spineLength t
        in TPLift True (IntroDef path (0, size) (toOntoModel (TermIKS t)) (rearrangeForSize [] 0 sp size True))
                :  map (\ i -> TPTransOp (TOFade Nothing) (TPAim (path ++ [i]))) [0 .. (sp - 1)]
    fuseHead'' t  =
        let sp = spineLength t
        in TPLift True (IntroDef path (0, size) (toOntoModel (TermBCKW t)) (rearrangeForSize [] 0 sp size True))
                :  map (\ i -> TPTransOp (TOFade Nothing) (TPAim (path ++ [i]))) [0 .. (sp - 1)]


together :: Maybe ([a],b->b) -> Maybe ([a],b->b) -> Maybe ([a],b->b)
together Nothing Nothing = Nothing
together l@(Just _) Nothing = l
together Nothing r@(Just _) = r
together (Just (ll,lf)) (Just (rl,rf)) = Just (ll ++ rl, lf . rf)



together' :: Maybe [a] -> Maybe [a] -> Maybe [a]
together' Nothing Nothing = Nothing
together' l@(Just _) Nothing = l
together' Nothing r@(Just _) = r
together' (Just l) (Just r) = Just (l ++ r)



