{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

\section[InstEnv]{Utilities for typechecking instance declarations}

The bits common to TcInstDcls and TcDeriv.
-}

{-# LANGUAGE CPP, DeriveDataTypeable, ScopedTypeVariables #-}

module InstEnv (
        DFunId, InstMatch, ClsInstLookupResult,
        OverlapFlag(..), OverlapMode(..), setOverlapModeMaybe,
        ClsInst(..), DFunInstType, pprInstance, pprInstanceHdr, pprInstances,
        instanceHead, instanceSig, mkLocalInstance, mkImportedInstance,
        instanceDFunId, tidyClsInstDFun, instanceRoughTcs,
        fuzzyClsInstCmp, orphNamesOfClsInst,

        InstEnvs(..), VisibleOrphanModules, InstEnv,
        emptyInstEnv, extendInstEnv, deleteFromInstEnv, identicalClsInstHead,
        extendInstEnvList, lookupUniqueInstEnv, lookupInstEnv, instEnvElts,
        memberInstEnv, instIsVisible,
        classInstances, instanceBindFun,
        instanceCantMatch, roughMatchTcs,
        isOverlappable, isOverlapping, isIncoherent
    ) where

#include "HsVersions.h"

import TcType -- InstEnv is really part of the type checker,
              -- and depends on TcType in many ways
import CoreSyn ( IsOrphan(..), isOrphan, chooseOrphanAnchor )
import Module
import Class
import Var
import VarSet
import Name
import NameSet
import Unify
import Outputable
import ErrUtils
import BasicTypes
import UniqFM
import Util
import Id
import Data.Data        ( Data )
import Data.Maybe       ( isJust, isNothing )

{-
************************************************************************
*                                                                      *
           ClsInst: the data type for type-class instances
*                                                                      *
************************************************************************
-}

data ClsInst
  = ClsInst {   -- Used for "rough matching"; see Note [Rough-match field]
                -- INVARIANT: is_tcs = roughMatchTcs is_tys
               is_cls_nm :: Name  -- Class name
             , is_tcs  :: [Maybe Name]  -- Top of type args

                -- Used for "proper matching"; see Note [Proper-match fields]
             , is_tvs  :: [TyVar]       -- Fresh template tyvars for full match
                                        -- See Note [Template tyvars are fresh]
             , is_cls  :: Class         -- The real class
             , is_tys  :: [Type]        -- Full arg types (mentioning is_tvs)
                -- INVARIANT: is_dfun Id has type
                --      forall is_tvs. (...) => is_cls is_tys
                -- (modulo alpha conversion)

             , is_dfun :: DFunId -- See Note [Haddock assumptions]

             , is_flag :: OverlapFlag   -- See detailed comments with
                                        -- the decl of BasicTypes.OverlapFlag
             , is_orphan :: IsOrphan
    }
  deriving Data

-- | A fuzzy comparison function for class instances, intended for sorting
-- instances before displaying them to the user.
fuzzyClsInstCmp :: ClsInst -> ClsInst -> Ordering
fuzzyClsInstCmp x y =
    stableNameCmp (is_cls_nm x) (is_cls_nm y) `mappend`
    mconcat (map cmp (zip (is_tcs x) (is_tcs y)))
  where
    cmp (Nothing, Nothing) = EQ
    cmp (Nothing, Just _) = LT
    cmp (Just _, Nothing) = GT
    cmp (Just x, Just y) = stableNameCmp x y

isOverlappable, isOverlapping, isIncoherent :: ClsInst -> Bool
isOverlappable i = hasOverlappableFlag (overlapMode (is_flag i))
isOverlapping  i = hasOverlappingFlag  (overlapMode (is_flag i))
isIncoherent   i = hasIncoherentFlag   (overlapMode (is_flag i))

{-
Note [Template tyvars are fresh]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The is_tvs field of a ClsInst has *completely fresh* tyvars.
That is, they are
  * distinct from any other ClsInst
  * distinct from any tyvars free in predicates that may
    be looked up in the class instance environment
Reason for freshness: we use unification when checking for overlap
etc, and that requires the tyvars to be distinct.

The invariant is checked by the ASSERT in lookupInstEnv'.

Note [Rough-match field]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
The is_cls_nm, is_tcs fields allow a "rough match" to be done
*without* poking inside the DFunId.  Poking the DFunId forces
us to suck in all the type constructors etc it involves,
which is a total waste of time if it has no chance of matching
So the Name, [Maybe Name] fields allow us to say "definitely
does not match", based only on the Name.

In is_tcs,
    Nothing  means that this type arg is a type variable

    (Just n) means that this type arg is a
                TyConApp with a type constructor of n.
                This is always a real tycon, never a synonym!
                (Two different synonyms might match, but two
                different real tycons can't.)
                NB: newtypes are not transparent, though!

Note [Proper-match fields]
~~~~~~~~~~~~~~~~~~~~~~~~~
The is_tvs, is_cls, is_tys fields are simply cached values, pulled
out (lazily) from the dfun id. They are cached here simply so
that we don't need to decompose the DFunId each time we want
to match it.  The hope is that the fast-match fields mean
that we often never poke the proper-match fields.

Note that:
 * is_tvs must be a superset of the free vars of is_tys
 * is_tvs must also be a superset of the free vars of theta
 * is_tvs must not be alpha-renamed from the dfunid,
   because it is used to substitute theta

Note [Haddock assumptions]
~~~~~~~~~~~~~~~~~~~~~~~~~~
For normal user-written instances, Haddock relies on

 * the SrcSpan of
 * the Name of
 * the is_dfun of
 * an Instance

being equal to

  * the SrcSpan of
  * the instance head type of
  * the InstDecl used to construct the Instance.
-}

instanceDFunId :: ClsInst -> DFunId
instanceDFunId = is_dfun

tidyClsInstDFun :: (DFunId -> DFunId) -> ClsInst -> ClsInst
tidyClsInstDFun tidy_dfun ispec
  = ispec { is_dfun = tidy_dfun (is_dfun ispec) }

instanceRoughTcs :: ClsInst -> [Maybe Name]
instanceRoughTcs = is_tcs


instance NamedThing ClsInst where
   getName ispec = getName (is_dfun ispec)

instance Outputable ClsInst where
   ppr = pprInstance

pprInstance :: ClsInst -> SDoc
-- Prints the ClsInst as an instance declaration
pprInstance ispec
  = hang (pprInstanceHdr ispec)
       2 (vcat [ text "--" <+> pprDefinedAt (getName ispec)
               , ifPprDebug (ppr (is_dfun ispec)) ])

-- * pprInstanceHdr is used in VStudio to populate the ClassView tree
pprInstanceHdr :: ClsInst -> SDoc
-- Prints the ClsInst as an instance declaration
pprInstanceHdr (ClsInst { is_flag = flag, is_dfun = dfun })
  = text "instance" <+> ppr flag <+> pprSigmaType (idType dfun)

pprInstances :: [ClsInst] -> SDoc
pprInstances ispecs = vcat (map pprInstance ispecs)

instanceHead :: ClsInst -> ([TyVar], Class, [Type])
-- Returns the head, using the fresh tyavs from the ClsInst
instanceHead (ClsInst { is_tvs = tvs, is_tys = tys, is_dfun = dfun })
   = (tvs, cls, tys)
   where
     (_, _, cls, _) = tcSplitDFunTy (idType dfun)

-- | Collects the names of concrete types and type constructors that make
-- up the head of a class instance. For instance, given `class Foo a b`:
--
-- `instance Foo (Either (Maybe Int) a) Bool` would yield
--      [Either, Maybe, Int, Bool]
--
-- Used in the implementation of ":info" in GHCi.
--
-- The 'tcSplitSigmaTy' is because of
--      instance Foo a => Baz T where ...
-- The decl is an orphan if Baz and T are both not locally defined,
--      even if Foo *is* locally defined
orphNamesOfClsInst :: ClsInst -> NameSet
orphNamesOfClsInst (ClsInst { is_cls_nm = cls_nm, is_tys = tys })
  = orphNamesOfTypes tys `unionNameSet` unitNameSet cls_nm

instanceSig :: ClsInst -> ([TyVar], [Type], Class, [Type])
-- Decomposes the DFunId
instanceSig ispec = tcSplitDFunTy (idType (is_dfun ispec))

mkLocalInstance :: DFunId -> OverlapFlag
                -> [TyVar] -> Class -> [Type]
                -> ClsInst
-- Used for local instances, where we can safely pull on the DFunId.
-- Consider using newClsInst instead; this will also warn if
-- the instance is an orphan.
mkLocalInstance dfun oflag tvs cls tys
  = ClsInst { is_flag = oflag, is_dfun = dfun
            , is_tvs = tvs
            , is_cls = cls, is_cls_nm = cls_name
            , is_tys = tys, is_tcs = roughMatchTcs tys
            , is_orphan = orph
            }
  where
    cls_name = className cls
    dfun_name = idName dfun
    this_mod = ASSERT( isExternalName dfun_name ) nameModule dfun_name
    is_local name = nameIsLocalOrFrom this_mod name

        -- Compute orphanhood.  See Note [Orphans] in InstEnv
    (cls_tvs, fds) = classTvsFds cls
    arg_names = [filterNameSet is_local (orphNamesOfType ty) | ty <- tys]

    -- See Note [When exactly is an instance decl an orphan?]
    orph | is_local cls_name = NotOrphan (nameOccName cls_name)
         | all notOrphan mb_ns  = ASSERT( not (null mb_ns) ) head mb_ns
         | otherwise         = IsOrphan

    notOrphan NotOrphan{} = True
    notOrphan _ = False

    mb_ns :: [IsOrphan]    -- One for each fundep; a locally-defined name
                           -- that is not in the "determined" arguments
    mb_ns | null fds   = [choose_one arg_names]
          | otherwise  = map do_one fds
    do_one (_ltvs, rtvs) = choose_one [ns | (tv,ns) <- cls_tvs `zip` arg_names
                                            , not (tv `elem` rtvs)]

    choose_one nss = chooseOrphanAnchor (unionNameSets nss)

mkImportedInstance :: Name
                   -> [Maybe Name]
                   -> DFunId
                   -> OverlapFlag
                   -> IsOrphan
                   -> ClsInst
-- Used for imported instances, where we get the rough-match stuff
-- from the interface file
-- The bound tyvars of the dfun are guaranteed fresh, because
-- the dfun has been typechecked out of the same interface file
mkImportedInstance cls_nm mb_tcs dfun oflag orphan
  = ClsInst { is_flag = oflag, is_dfun = dfun
            , is_tvs = tvs, is_tys = tys
            , is_cls_nm = cls_nm, is_cls = cls, is_tcs = mb_tcs
            , is_orphan = orphan }
  where
    (tvs, _, cls, tys) = tcSplitDFunTy (idType dfun)

{-
Note [When exactly is an instance decl an orphan?]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  (see MkIface.instanceToIfaceInst, which implements this)
Roughly speaking, an instance is an orphan if its head (after the =>)
mentions nothing defined in this module.

Functional dependencies complicate the situation though. Consider

  module M where { class C a b | a -> b }

and suppose we are compiling module X:

  module X where
        import M
        data T = ...
        instance C Int T where ...

This instance is an orphan, because when compiling a third module Y we
might get a constraint (C Int v), and we'd want to improve v to T.  So
we must make sure X's instances are loaded, even if we do not directly
use anything from X.

More precisely, an instance is an orphan iff

  If there are no fundeps, then at least of the names in
  the instance head is locally defined.

  If there are fundeps, then for every fundep, at least one of the
  names free in a *non-determined* part of the instance head is
  defined in this module.

(Note that these conditions hold trivially if the class is locally
defined.)


************************************************************************
*                                                                      *
                InstEnv, ClsInstEnv
*                                                                      *
************************************************************************

A @ClsInstEnv@ all the instances of that class.  The @Id@ inside a
ClsInstEnv mapping is the dfun for that instance.

If class C maps to a list containing the item ([a,b], [t1,t2,t3], dfun), then

        forall a b, C t1 t2 t3  can be constructed by dfun

or, to put it another way, we have

        instance (...) => C t1 t2 t3,  witnessed by dfun
-}

---------------------------------------------------
type InstEnv = UniqFM ClsInstEnv        -- Maps Class to instances for that class

-- | 'InstEnvs' represents the combination of the global type class instance
-- environment, the local type class instance environment, and the set of
-- transitively reachable orphan modules (according to what modules have been
-- directly imported) used to test orphan instance visibility.
data InstEnvs = InstEnvs {
        ie_global  :: InstEnv,               -- External-package instances
        ie_local   :: InstEnv,               -- Home-package instances
        ie_visible :: VisibleOrphanModules   -- Set of all orphan modules transitively
                                             -- reachable from the module being compiled
                                             -- See Note [Instance lookup and orphan instances]
    }

-- | Set of visible orphan modules, according to what modules have been directly
-- imported.  This is based off of the dep_orphs field, which records
-- transitively reachable orphan modules (modules that define orphan instances).
type VisibleOrphanModules = ModuleSet

newtype ClsInstEnv
  = ClsIE [ClsInst]    -- The instances for a particular class, in any order

instance Outputable ClsInstEnv where
  ppr (ClsIE is) = pprInstances is

-- INVARIANTS:
--  * The is_tvs are distinct in each ClsInst
--      of a ClsInstEnv (so we can safely unify them)

-- Thus, the @ClassInstEnv@ for @Eq@ might contain the following entry:
--      [a] ===> dfun_Eq_List :: forall a. Eq a => Eq [a]
-- The "a" in the pattern must be one of the forall'd variables in
-- the dfun type.

emptyInstEnv :: InstEnv
emptyInstEnv = emptyUFM

instEnvElts :: InstEnv -> [ClsInst]
instEnvElts ie = [elt | ClsIE elts <- eltsUFM ie, elt <- elts]

-- | Test if an instance is visible, by checking that its origin module
-- is in 'VisibleOrphanModules'.
-- See Note [Instance lookup and orphan instances]
instIsVisible :: VisibleOrphanModules -> ClsInst -> Bool
instIsVisible vis_mods ispec
  -- NB: Instances from the interactive package always are visible. We can't
  -- add interactive modules to the set since we keep creating new ones
  -- as a GHCi session progresses.
  | isInteractiveModule mod     = True
  | IsOrphan <- is_orphan ispec = mod `elemModuleSet` vis_mods
  | otherwise                   = True
  where
    mod = nameModule (idName (is_dfun ispec))

classInstances :: InstEnvs -> Class -> [ClsInst]
classInstances (InstEnvs { ie_global = pkg_ie, ie_local = home_ie, ie_visible = vis_mods }) cls
  = get home_ie ++ get pkg_ie
  where
    get env = case lookupUFM env cls of
                Just (ClsIE insts) -> filter (instIsVisible vis_mods) insts
                Nothing            -> []

-- | Checks for an exact match of ClsInst in the instance environment.
-- We use this when we do signature checking in TcRnDriver
memberInstEnv :: InstEnv -> ClsInst -> Bool
memberInstEnv inst_env ins_item@(ClsInst { is_cls_nm = cls_nm } ) =
    maybe False (\(ClsIE items) -> any (identicalClsInstHead ins_item) items)
          (lookupUFM inst_env cls_nm)

extendInstEnvList :: InstEnv -> [ClsInst] -> InstEnv
extendInstEnvList inst_env ispecs = foldl extendInstEnv inst_env ispecs

extendInstEnv :: InstEnv -> ClsInst -> InstEnv
extendInstEnv inst_env ins_item@(ClsInst { is_cls_nm = cls_nm })
  = addToUFM_C add inst_env cls_nm (ClsIE [ins_item])
  where
    add (ClsIE cur_insts) _ = ClsIE (ins_item : cur_insts)

deleteFromInstEnv :: InstEnv -> ClsInst -> InstEnv
deleteFromInstEnv inst_env ins_item@(ClsInst { is_cls_nm = cls_nm })
  = adjustUFM adjust inst_env cls_nm
  where
    adjust (ClsIE items) = ClsIE (filterOut (identicalClsInstHead ins_item) items)

identicalClsInstHead :: ClsInst -> ClsInst -> Bool
-- ^ True when when the instance heads are the same
-- e.g.  both are   Eq [(a,b)]
-- Used for overriding in GHCi
-- Obviously should be insenstive to alpha-renaming
identicalClsInstHead (ClsInst { is_cls_nm = cls_nm1, is_tcs = rough1, is_tys = tys1 })
                     (ClsInst { is_cls_nm = cls_nm2, is_tcs = rough2, is_tys = tys2 })
  =  cls_nm1 == cls_nm2
  && not (instanceCantMatch rough1 rough2)  -- Fast check for no match, uses the "rough match" fields
  && isJust (tcMatchTys tys1 tys2)
  && isJust (tcMatchTys tys2 tys1)

{-
************************************************************************
*                                                                      *
        Looking up an instance
*                                                                      *
************************************************************************

@lookupInstEnv@ looks up in a @InstEnv@.
We now use *unification* to look up instances, rather than the previous
matching. Matching returns too few instances; consider
     A a [c]
in an InstEnv that has
     A [b] b
Previously, GHC would not instantiate this, since it would generate a
constraint
     a ~ [[c]]
But such a constraint is perfectly acceptable.
It does not add any ambiguity, because the check for overlap
used unification regardless.

Note [Instance lookup and orphan instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Suppose we are compiling a module M, and we have a zillion packages
loaded, and we are looking up an instance for C (T W).  If we find a
match in module 'X' from package 'p', should be "in scope"; that is,

  is p:X in the transitive closure of modules imported from M?

The difficulty is that the "zillion packages" might include ones loaded
through earlier invocations of the GHC API, or earlier module loads in GHCi.
They might not be in the dependencies of M itself; and if not, the instances
in them should not be visible.  Trac #2182, #8427.

There are two cases:
  * If the instance is *not an orphan*, then module X defines C, T, or W.
    And in order for those types to be involved in typechecking M, it
    must be that X is in the transitive closure of M's imports.  So we
    can use the instance.

  * If the instance *is an orphan*, the above reasoning does not apply.
    So we keep track of the set of orphan modules transitively below M;
    this is the ie_visible field of InstEnvs, of type VisibleOrphanModules.

    If module p:X is in this set, then we can use the instance, otherwise
    we can't.

Note [Rules for instance lookup]
Note [Overlapping instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
These functions implement the carefully-written rules in the user
manual section on "overlapping instances". At risk of duplication,
here are the rules.  If the rules change, change this text and the
user manual simultaneously.  The link may be this:
http://www.haskell.org/ghc/docs/latest/html/users_guide/type-class-extensions.html#instance-overlap

The willingness to be overlapped or incoherent is a property of the
instance declaration itself, controlled as follows:

 * An instance is "incoherent"
   if it has an INCOHERENT pragma, or
   if it appears in a module compiled with -XIncoherentInstances.

 * An instance is "overlappable"
   if it has an OVERLAPPABLE or OVERLAPS pragma, or
   if it appears in a module compiled with -XOverlappingInstances, or
   if the instance is incoherent.

 * An instance is "overlapping"
   if it has an OVERLAPPING or OVERLAPS pragma, or
   if it appears in a module compiled with -XOverlappingInstances, or
   if the instance is incoherent.
     compiled with -XOverlappingInstances.

Now suppose that, in some client module, we are searching for an instance
of the target constraint (C ty1 .. tyn). The search works like this.

 * Find all instances that unify with the target constraint.
   These instance declarations are the candidates.

 * The candidates are considered in order, least specific to most specific,
   then first declared to later declared, but this only matters for
   incoherent instances.

 * Eliminate any candidate IX when there is another candidate IY
   and either of the following holds:
   (A) IX is incoherent
   (B) IX is marked overlappable or IY is marked overlapping, AND
       IY is strictly more specific than IX; that is, IY is a substitution
        instance of IX, but not vice versa.

 * If only one candidate remains, pick it. Otherwise fail.

Note [Incoherent instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
For some classes, the choice of a particular instance does not matter, any one
is good. Consider

        class D a b where { opD :: a -> b -> String }
        foo :: x -> y -> String
        foo x y = show x ++ show y
        instance (Show b) => D Int b where opD = foo
        instance (Show a) => D a Bool where opD = foo

        f = opD :: Int -> Char -> String -- works
        g = opD :: Int -> Bool -> String -- fails; overlapping instances

We could fix this by adding an instance {-# OVERLAPPING #-} D Int Bool, but
in general working through all of the cases would be tedious. This is what
-XIncoherentInstances is for: Telling GHC "I don't care which instance you use;
if you can use one, use it."

Note that, due to the rules about discarding incoherent instances, there will be
no overlap even if all but one instance is incoherent.
Example:
        class C a b c where foo :: (a,b,c)
        instance C [a] b Int
        instance {-# incoherent #-} C [Int] b c
        instance {-# incoherent #-} C a   Int c
Thanks to the incoherent flags, these are both instantiated with the first instance:
        x = foo :: ([a]  ,b  ,Int)
        y = foo :: ([Int],Int,Int)
This is based on the behavior of earlier GHC implementations.

Note [Avoiding a problem with overlapping]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider 'd' in testsuite/tests/typecheck/should_run/SuperclassOverlap.hs
We have two dictionaries in scope, a 'C [a]' instance from the superclass constraint, and the normal 'C [a]' instance.
The GHC policy is to always prefer Givens to environmental instances, so our program should print [2].

Note [Binding when looking up instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

See testsuite/tests/typecheck/should_compile/tc179.hs.

The op [x,x] means we need (Foo [a]).  Without the filterVarSet we'd
complain, saying that the choice of instance depended on the instantiation
of 'a'; but of course it isn't *going* to be instantiated.

We do this only for isOverlappableTyVar skolems.  For example we reject
        g :: forall a => [a] -> Int
        g x = op x
on the grounds that the correct instance depends on the instantiation of 'a'

The key_tys can contain skolem constants, and we can guarantee that those
are never going to be instantiated to anything, so we should not involve
them in the unification test.  Example:

Note [DFunInstType: instantiating types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A successful match is a ClsInst, together with a template substitution.
        dfun :: forall a b. C a b, Ord b => D [a]
When we match this against D [ty], we return the substitution
        [a -> ty]
where absence of 'b' indicates that it can be freely instantiated.

The caller thus needs to know that 'b' is unbound, and create a fresh variable.

Similarly, solving:
    class A x y
    instance A b [c]
    foo :: (A [a] a) => (a,a)
we get:
    b -> [[c]], a -> [c]
Then c has to be replaced with a fresh d (a flexi type variable,
which can be fixed later by fundeps etc.):
    b -> [[d]], a -> [d]
It is assumed that the caller does this, if it uses the substitution.

Finally, for this:
    class A x y
    instance A [b] b
    foo :: (A a [c]) => (a,c)
we get as solution to the unification:
    a -> [[c]], b -> [c]
c is not replaced with a fresh variable, because it's part of the given constraint.
The caller must add the constraint a ~ [[c]] to the environment.
-}

type DFunInstType = Maybe Type
        -- Just ty   => Instantiate with this type
        -- Nothing   => Instantiate with any type of this tyvar's kind
        -- See Note [DFunInstType: instantiating types]

type InstMatch = (ClsInst, TCvSubst)

type ClsInstLookupResult
     = ( [InstMatch]     -- Successful matches (only instantiated if a unique instance is found)
       , [InstMatch] )   -- Unsafe overlapped instances under Safe Haskell
                         -- (see Note [Safe Haskell Overlapping Instances] in
                         -- TcSimplify).

-- |Look up an instance in the given instance environment. The given class application must match exactly
-- one instance and the unification must bind all class type variables.  If the lookup is unsuccessful,
-- yield 'Left errorMessage'.
lookupUniqueInstEnv :: InstEnvs
                    -> Class -> [Type]
                    -> Either MsgDoc (ClsInst, [Type])
lookupUniqueInstEnv instEnv cls tys
  = case lookupInstEnv False instEnv cls tys of
      ([(inst, subst)], _)
             | noFlexiVar -> Right (inst, inst_tys')
             | otherwise  -> Left $ text "flexible type variable:" <+>
                                    (ppr $ mkTyConApp (classTyCon cls) tys)
             where
               inst_tys = map (lookupTyVar subst) (is_tvs inst)
               inst_tys'  = [ty | Just ty <- inst_tys]
               noFlexiVar = all isJust inst_tys
      _other -> Left $ text "no unique instance found:" <+>
                       (ppr $ mkTyConApp (classTyCon cls) tys)

lookupInstEnv' :: InstEnv          -- InstEnv to look in
               -> VisibleOrphanModules   -- But filter against this
               -> Class -> [Type]  -- What we are looking for
               -> [InstMatch] -- Successful unifications
lookupInstEnv' ie vis_mods cls tys
  = lookup ie
  where
    rough_tcs  = roughMatchTcs tys
    all_tvs    = all isNothing rough_tcs

    --------------
    lookup env = case lookupUFM env cls of
                   Nothing -> []   -- No instances for this class
                   Just (ClsIE insts) -> find [] insts

    --------------
    find ms [] = ms
    find ms (item@(ClsInst { is_tcs = mb_tcs, is_tvs = tpl_tvs
                                , is_tys = tpl_tys }) : rest)
      | not (instIsVisible vis_mods item)
      = find ms rest  -- See Note [Instance lookup and orphan instances]

        -- Fast check for no match, uses the "rough match" fields
      | instanceCantMatch rough_tcs mb_tcs
      = find ms rest

      | Just subst <- ASSERT2( tyCoVarsOfTypes tys `disjointVarSet` tpl_tv_set,
                               (ppr cls <+> ppr tys <+> ppr all_tvs) $$
                               (ppr tpl_tvs <+> ppr tpl_tys)
                             )
                      tcUnifyTys instanceBindFun tpl_tys tys
                      -- Unification will break badly if the variables overlap
                      -- They shouldn't because we allocate separate uniques for them
                      -- See Note [Template tyvars are fresh]
      = find ((item, subst) : ms) rest

        -- Does not match, keep looking
      | otherwise
      = find ms rest
      where
        tpl_tv_set = mkVarSet tpl_tvs

---------------
-- This is the common way to call this function.
lookupInstEnv :: Bool              -- Check Safe Haskell overlap restrictions
              -> InstEnvs          -- External and home package inst-env
              -> Class -> [Type]   -- What we are looking for
              -> ClsInstLookupResult
-- ^ See Note [Rules for instance lookup]
-- ^ See Note [Safe Haskell Overlapping Instances] in TcSimplify
-- ^ See Note [Safe Haskell Overlapping Instances Implementation] in TcSimplify
lookupInstEnv check_overlap_safe
              (InstEnvs { ie_global = pkg_ie
                        , ie_local = home_ie
                        , ie_visible = vis_mods })
              cls
              tys
  = -- pprTrace "lookupInstEnv" (ppr cls <+> ppr tys $$ ppr home_ie) $
    (final_matches, unsafe_overlapped)
  where
    home_unifs = lookupInstEnv' home_ie vis_mods cls tys
    pkg_unifs  = lookupInstEnv' pkg_ie  vis_mods cls tys
    all_unifs  = home_unifs ++ pkg_unifs
    final_matches = foldr insert_overlapping [] all_unifs

    unsafe_overlapped
       = case final_matches of
           [match] -> check_safe match
           _       -> []

    -- NOTE [Safe Haskell isSafeOverlap]
    -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    -- We restrict code compiled in 'Safe' mode from overriding code
    -- compiled in any other mode. The rationale is that code compiled
    -- in 'Safe' mode is code that is untrusted by the ghc user. So
    -- we shouldn't let that code change the behaviour of code the
    -- user didn't compile in 'Safe' mode since that's the code they
    -- trust. So 'Safe' instances can only overlap instances from the
    -- same module. A same instance origin policy for safe compiled
    -- instances.
    check_safe (inst,_)
        = case check_overlap_safe && unsafeTopInstance inst of
                -- make sure it only overlaps instances from the same module
                True -> go [] all_unifs
                -- most specific is from a trusted location.
                False -> []
        where
            go bad [] = bad
            go bad (i@(x,_):unchecked) =
                if inSameMod x || isOverlappable x
                    then go bad unchecked
                    else go (i:bad) unchecked

            inSameMod b =
                let na = getName $ getName inst
                    la = isInternalName na
                    nb = getName $ getName b
                    lb = isInternalName nb
                in (la && lb) || (nameModule na == nameModule nb)

    -- We check if the most specific instance is unsafe when it both:
    --   (1) Comes from a module compiled as `Safe`
    --   (2) Is an orphan instance, OR, an instance for a MPTC
    unsafeTopInstance inst = isSafeOverlap (is_flag inst) &&
        (isOrphan (is_orphan inst) || classArity (is_cls inst) > 1)

    insert_overlapping :: InstMatch -> [InstMatch] -> [InstMatch]
    -- ^ Add a new solution, knocking out strictly less specific ones
    -- See Note [Rules for instance lookup]
    insert_overlapping new_item [] = [new_item]
    insert_overlapping new_item@(new_inst,_) (old_item@(old_inst,_) : old_items)
      | new_beats_old        -- New strictly overrides old
      , not old_beats_new
      , new_inst `can_override` old_inst
      = insert_overlapping new_item old_items

      | old_beats_new        -- Old strictly overrides new
      , not new_beats_old
      , old_inst `can_override` new_inst
      = old_item : old_items

      -- Discard incoherent instances; see Note [Incoherent instances]
      | isIncoherent old_inst      -- Old is incoherent; discard it
      = insert_overlapping new_item old_items
      | isIncoherent new_inst      -- New is incoherent; discard it
      = old_item : old_items

      -- Equal or incomparable, and neither is incoherent; keep both
      | otherwise
      = old_item : insert_overlapping new_item old_items
      where

        new_beats_old = new_inst `more_specific_than` old_inst
        old_beats_new = old_inst `more_specific_than` new_inst

        -- `instB` can be instantiated to match `instA`
        -- or the two are equal
        instA `more_specific_than` instB
          = isJust (tcMatchTys (is_tys instB) (is_tys instA))

        instA `can_override` instB
          = isOverlapping instA || isOverlappable instB
          -- Overlap permitted if either the more specific instance
          -- is marked as overlapping, or the more general one is
          -- marked as overlappable.
          -- See [Rules for instance lookup], Trac #9242, Trac #3877

instanceBindFun :: TyCoVar -> BindFlag
instanceBindFun tv | isTcTyVar tv && isOverlappableTyVar tv = Skolem
                   | otherwise                              = BindMe
   -- Note [Binding when looking up instances]
