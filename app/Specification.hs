{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module PTS where

import Control.Monad (void)
import Control.Lens (preview, view)
import Data.Aeson (FromJSON, ToJSON)
import Data.Either.Combinators (rightToMaybe)
import Data.Maybe (fromMaybe)
import Data.Monoid (Last (Last))
import GHC.Generics
import Text.Printf (printf)
import qualified Data.Map as Map
import qualified Ledger
import qualified Ledger.Ada as Ada
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Scripts as Scripts
import qualified Ledger.Typed.Scripts as TScripts
import qualified Ledger.Value as Value
import qualified Plutus.Contract as Contract
import qualified Plutus.Contracts.Currency as Currency
import qualified Plutus.Trace.Emulator as Trace
import qualified PlutusTx
import qualified PlutusTx.Eq as Eq
import qualified PlutusTx.Prelude as PL
import qualified PlutusTx.Numeric as PNum
import qualified PlutusTx.Ord as POrd
import PlutusTx.Trace (traceIfFalse, traceError)	
import Wallet.Emulator (knownWallet)
import Prelude
    
data CDPAction = XOpen {oPubKey :: Ledger.PubKeyHash} | 
	        XDeposit {dPubKey :: Ledger.PubKeyHash, dAmount :: Integer} | 
	        XWithdraw {wPubKey :: Ledger.PubKeyHash, wAmount :: Integer} | 
	        XMint {mPubKey :: Ledger.PubKeyHash, mAmount :: Integer} | 
	        XBurn {bPubKey :: Ledger.PubKeyHash, bAmount :: Integer}
	deriving Show

PlutusTx.unstableMakeIsData ''CDPAction

data CDPDatum = ManagerDatum {pkhList :: [Ledger.PubKeyHash]} |
                UserDatum {myPubKey :: Ledger.PubKeyHash, myLockedAda :: Integer, myMintedToken :: Integer}
		  deriving Show
             
PlutusTx.unstableMakeIsData ''CDPDatum

data CDP

instance TScripts.ValidatorTypes CDP where
    type DatumType CDP = CDPDatum
    type RedeemerType CDP = CDPAction

data CDParams = CDParams {getManagerT :: Value.AssetClass, getUserT :: Value.AssetClass}

PlutusTx.unstableMakeIsData ''CDParams
PlutusTx.makeLift ''CDParams

data EPInput = EPInput { epManagerT :: Value.AssetClass, epUserT :: Value.AssetClass, epAmount :: Integer }
		deriving (Show, ToJSON, FromJSON, Generic, Monoid, Semigroup)

PlutusTx.unstableMakeIsData ''EPInput

getDatum :: PlutusTx.FromData b => Ledger.ChainIndexTxOut -> Maybe b
getDatum o = preview Ledger.ciTxOutDatum o >>= rightToMaybe >>= (PlutusTx.fromBuiltinData.Ledger.getDatum)

getValue :: Ledger.ChainIndexTxOut -> Ledger.Value
getValue = view Ledger.ciTxOutValue

isManagerOutput :: Value.AssetClass -> Ledger.ChainIndexTxOut -> Bool
isManagerOutput nft inp = case getDatum @CDPDatum inp of
    Just (ManagerDatum _) -> (Ledger._ciTxOutValue inp) == (Value.assetClassValue nft 1)
    _                     -> False

isUserCollateralOutput :: Value.AssetClass -> Ledger.PubKeyHash -> Ledger.ChainIndexTxOut -> Bool
isUserCollateralOutput utk x inp = case getDatum @CDPDatum inp of
    Just (UserDatum y mon _) -> x == y && chkUserVal (Ledger._ciTxOutValue inp)
    _                        -> False
    where
        chkUserVal :: Value.Value -> Bool
        chkUserVal val = foldl (||) False [ Value.assetClass a b == utk && c == 1 | (a,b,c) <- Value.flattenValue val]
eqAssetClass :: Value.AssetClass -> Value.AssetClass -> Bool
eqAssetClass a b = fst (Value.unAssetClass a) Eq.== fst (Value.unAssetClass b) &&
                   snd (Value.unAssetClass a) Eq.== snd (Value.unAssetClass b)

collateralRatio :: Double
collateralRatio = 1.5

managerNFTTokenName :: Value.TokenName
managerNFTTokenName = "iTSLA-Manager"

{-# INLINEABLE mkValidator #-}
mkValidator :: CDParams -> CDPDatum -> CDPAction -> Ledger.ScriptContext -> Bool
mkValidator cp dat opts ctx = case opts of
	XOpen p -> case dat of
	    UserDatum _ _ _  -> False
	    ManagerDatum xs  -> 
	        traceIfFalse "Signature Invalid" (signedByUser $ oPubKey (XOpen p)) &&
	        traceIfFalse "Invalid output user datum" (checkUserDatum p 0 0) &&
	        traceIfFalse "Invalid Manager datum list" (managerDatumList p) &&
	        traceIfFalse "User already opened" (not $ p `PL.elem` xs) &&
	        traceIfFalse "Manager NFT not at input value" (nftVal == inVal) &&
	        traceIfFalse "Manager NFT not at output value" (checkManagerOutputValue nftVal) &&
	        traceIfFalse "User NFT not at output value" (checkUserOutputValue userVal)
	XDeposit _ x -> case dat of
	    ManagerDatum _ -> False
	    UserDatum p lok min ->
	        traceIfFalse "Signature Invalid" (signedByUser $ p) &&
	        traceIfFalse "Invalid output user datum" (checkUserDatum p (lok PNum.+ x) min) &&
	        traceIfFalse "Wrong input value" (inVal == userVal <> Ada.lovelaceValueOf lok) &&
	        traceIfFalse "Output value mismatch" (checkUserOutputValue (userVal <> Ada.lovelaceValueOf (lok PNum.+ x))) &&
	        traceIfFalse "Negative deposit value found" (x POrd.> 0)      
	XWithdraw _ x -> case dat of
	    ManagerDatum _ -> False
	    UserDatum p lok min ->
	        traceIfFalse "Signature Invalid" (signedByUser $ p) &&
	        traceIfFalse "Insufficient balance" (x POrd.<= lok) &&
	        traceIfFalse "Invalid output user datum" (checkUserDatum p (lok PNum.- x) min) &&
	        traceIfFalse "Wrong input value" (inVal == userVal <> Ada.lovelaceValueOf lok) &&
	        traceIfFalse "Output value mismatch" (checkUserOutputValue (userVal <> Ada.lovelaceValueOf (lok PNum.- x))) &&
	        traceIfFalse "Invalid withdraw amount" (x POrd.>0 && x POrd.<=lok) && 
	        traceIfFalse "Broken collateral ratio" (maintainCR (lok PNum.- x) min)
	XMint _ x -> case dat of
	    ManagerDatum _ -> False
	    UserDatum p lok min ->
	        traceIfFalse "Signature Invalid" (signedByUser $ p) &&
	        traceIfFalse "Invalid mint amount" (x POrd.>0) &&
	        traceIfFalse "Wrong input value" (inVal == userVal <> Ada.lovelaceValueOf lok) &&
	        traceIfFalse "Invalid output user datum" (checkUserDatum p lok (min PNum.+ x)) &&
	        traceIfFalse "Output value mismatch" (checkUserOutputValue (userVal <> Ada.lovelaceValueOf lok)) &&
	        traceIfFalse "Broken collateral ratio" (maintainCR lok (min PNum.+ x))
	XBurn _ x -> case dat of
	    ManagerDatum _  -> False
	    UserDatum p lok min  ->
	        traceIfFalse "Signature Invalid" (signedByUser $ p) &&
	        traceIfFalse "Invalid burn amount" (x POrd.>0 && x POrd.<= min) &&
	        traceIfFalse "Wrong input value" (inVal == userVal <> Ada.lovelaceValueOf lok) &&
	        traceIfFalse "Invalid output user datum" (checkUserDatum p lok (min PNum.- x)) &&
	        traceIfFalse "Output value mismatch" (checkUserOutputValue (userVal <> Ada.lovelaceValueOf lok))
	        
  where
    info :: Ledger.TxInfo
    info = Ledger.scriptContextTxInfo ctx
    
    input :: Ledger.TxInInfo
    input =
      let
        isScriptInput i = case (Ledger.txOutDatumHash . Ledger.txInInfoResolved) i of
            Nothing -> False
            Just _  -> True
        xs = [i | i <- Ledger.txInfoInputs info, isScriptInput i]
      in
        case xs of
            [i] -> i
            _   -> traceError "expected exactly one script input"
    
    ownOutput :: [Ledger.TxOut]
    ownOutput = Ledger.getContinuingOutputs ctx
    
    inVal :: Value.Value
    inVal = Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    nftVal :: Value.Value
    nftVal = (Value.assetClassValue (getManagerT cp) 1)
    
    userVal :: Value.Value
    userVal = (Value.assetClassValue (getUserT cp) 1)
    
    ownInput :: Ledger.TxOut
    ownInput = case Ledger.findOwnInput ctx of
      Nothing -> traceError "Expected input"
      Just i -> Ledger.txInInfoResolved i
    
    isManager :: Ledger.TxOut -> Bool
    isManager os = case outputDatum os (`Ledger.findDatum` info) of
      Just (ManagerDatum _) -> True
      _ -> False

    isUser :: Ledger.TxOut -> Bool
    isUser os = case outputDatum os (`Ledger.findDatum` info) of
      Just (UserDatum _ _ _) -> True
      _ -> False
    
    checkUserOutputValue :: Value.Value -> Bool
    checkUserOutputValue v = v == (Ledger.txOutValue outUserOutput)
    
    checkManagerOutputValue :: Value.Value -> Bool
    checkManagerOutputValue v = v == (Ledger.txOutValue outManagerOutput)
    
    outManagerOutput :: Ledger.TxOut
    outManagerOutput = case PL.filter isManager ownOutput of
      [o] -> o
      _   -> traceError "Expected exactly one Manager output"
    
    outUserOutput :: Ledger.TxOut
    outUserOutput = case PL.filter isUser ownOutput of
      [o] -> o
      _   -> traceError "Expected exactly one User output"
      
    outManagerDatum :: CDPDatum
    outManagerDatum = case outputDatum outManagerOutput (`Ledger.findDatum` info) of
      Just a -> a
      _ -> traceError "Impossible case"
    
    outUserDatum :: CDPDatum
    outUserDatum = case outputDatum outUserOutput (`Ledger.findDatum` info) of
      Just a -> a
      _ -> traceError "Impossible case"
    
    managerDatumList :: Ledger.PubKeyHash -> Bool
    managerDatumList k = case dat of
      ManagerDatum l -> 
        case outManagerDatum of
          ManagerDatum (a:as) -> a Eq.== k && l Eq.== as
          _ -> traceError "Invalid manager output datum"
      _ -> traceError "Wrong manager input datum"
    
    checkUserDatum :: Ledger.PubKeyHash -> Integer -> Integer -> Bool
    checkUserDatum k lk mt = case outUserDatum of
      UserDatum k' lk' mt' -> k Eq.== k' && lk' Eq.== lk && mt' Eq.== mt
      _ -> traceError "Wrong user input datum"
    

    outputDatum :: Ledger.TxOut  -> (Scripts.DatumHash -> Maybe Scripts.Datum) -> Maybe CDPDatum
    outputDatum o f = do
      dh <- Ledger.txOutDatum o
      Scripts.Datum d <- f dh
      PlutusTx.fromBuiltinData d
    
    signedByUser :: Ledger.PubKeyHash -> Bool
    signedByUser = Ledger.txSignedBy info
    
    maintainCR :: Integer -> Integer -> Bool
    maintainCR x y = adaPrice PNum.* x POrd.>= collateralR PNum.* crAsset PNum.* y PNum.* (10000 :: Integer)
    
    adaPrice :: Integer
    adaPrice = 13
    
    collateralR :: Integer
    collateralR = 15
    
    crAsset :: Integer
    crAsset  = 70967
    
cdpInstance :: CDParams -> TScripts.TypedValidator CDP
cdpInstance cp =
  TScripts.mkTypedValidator @CDP
    ($$(PlutusTx.compile [||mkValidator||]) `PlutusTx.applyCode` PlutusTx.liftCode cp)
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TScripts.wrapValidator @CDPDatum @CDPAction

cdpValidator :: CDParams -> TScripts.Validator
cdpValidator = TScripts.validatorScript. cdpInstance

cdpValidatorHash :: CDParams -> Ledger.ValidatorHash
cdpValidatorHash = TScripts.validatorHash. cdpInstance

cdpAddress :: CDParams -> Ledger.Address
cdpAddress = Ledger.scriptAddress. cdpValidator

{-# INLINEABLE mkPolicy #-}
mkPolicy :: Value.AssetClass -> () -> Ledger.ScriptContext -> Bool
mkPolicy utk _ ctx = traceIfFalse "Need user CDP" needOneUser
  where
    info :: Ledger.TxInfo
    info = Ledger.scriptContextTxInfo ctx
    
    input :: Ledger.TxInInfo
    input =
      let
        isScriptInput i = case (Ledger.txOutDatumHash . Ledger.txInInfoResolved) i of
            Nothing -> False
            Just _  -> True
        xs = [i | i <- Ledger.txInfoInputs info, isScriptInput i]
      in
        case xs of
            [i] -> i
            _   -> traceError "expected exactly one script input"
            
    inVal :: Value.Value
    inVal = Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    needOneUser :: Bool
    needOneUser =
      let
        findUsr :: (Value.CurrencySymbol, Value.TokenName, Integer) -> Bool
        findUsr (cs, tn, _) = utk Eq.== (Value.assetClass cs tn)
        xs = PL.filter findUsr (Value.flattenValue inVal)
      in
        case xs of
          [_] -> True
          _   -> False
        
mintingPolicy :: Value.AssetClass -> TScripts.MintingPolicy
mintingPolicy ac =
  Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy . mkPolicy||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode ac

mintingPolicyHash :: Value.AssetClass -> Scripts.MintingPolicyHash
mintingPolicyHash = Scripts.mintingPolicyHash. mintingPolicy

myCurrencySymbol :: Value.AssetClass -> Value.CurrencySymbol
myCurrencySymbol = Value.mpsSymbol.mintingPolicyHash

myTokenName :: Value.TokenName
myTokenName = "iTSLA"

{-# INLINEABLE mkUserPolicy #-} -- 

mkUserPolicy :: Value.AssetClass -> () -> Ledger.ScriptContext -> Bool
mkUserPolicy ac _ ctx = traceIfFalse "Input does not contain manager NFT" (nftVal == inVal) &&
                        traceIfFalse "Only 1 user token is allowed to be minted for each user" mintedAmount
  where
    info :: Ledger.TxInfo
    info  = Ledger.scriptContextTxInfo ctx
    
    input :: Ledger.TxInInfo  
    input =
      let
        isScriptInput i = case (Ledger.txOutDatumHash . Ledger.txInInfoResolved) i of
            Nothing -> False
            Just _  -> True
        xs = [i | i <- Ledger.txInfoInputs info, isScriptInput i]
      in
        case xs of
            [i] -> i
            _   -> traceError "expected exactly one script input"
    inVal :: Value.Value
    inVal = Ledger.txOutValue . Ledger.txInInfoResolved $ input
    
    nftVal :: Value.Value
    nftVal = (Value.assetClassValue ac 1)
    
    isManager :: Ledger.TxOut -> Bool
    isManager os = case outputDatum os (`Ledger.findDatum` info) of
      Just (ManagerDatum _) -> True
      _ -> False
    
    outputManager :: Ledger.TxOut
    outputManager = Ledger.txInInfoResolved input
    
    outputDatum :: Ledger.TxOut  -> (Scripts.DatumHash -> Maybe Scripts.Datum) -> Maybe CDPDatum
    outputDatum o f = do
      dh <- Ledger.txOutDatum o
      Scripts.Datum d <- f dh
      PlutusTx.fromBuiltinData d
    
    mintedAmount :: Bool
    mintedAmount = case (Value.flattenValue (Ledger.txInfoMint info)) of
      [(cs',tk', amt)] -> amt Eq.== 1
      _            -> False
      
userMintingPolicy :: Value.AssetClass -> TScripts.MintingPolicy
userMintingPolicy ac =
  Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [|| TScripts.wrapMintingPolicy. mkUserPolicy||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode ac

userMintingPolicyHash :: Value.AssetClass -> Scripts.MintingPolicyHash
userMintingPolicyHash = Scripts.mintingPolicyHash . userMintingPolicy

userCurrencySymbol :: Value.AssetClass -> Value.CurrencySymbol
userCurrencySymbol = Value.mpsSymbol . userMintingPolicyHash

userTokenName :: Value.TokenName
userTokenName = "iTSLA-User"

type InitSchema = Contract.Endpoint "Init" ()

type CDPSchema = Contract.Endpoint "Open" EPInput Contract..\/
	        Contract.Endpoint "Deposit" EPInput Contract..\/ 
	        Contract.Endpoint "Withdraw" EPInput Contract..\/ 
	        Contract.Endpoint "Mint" EPInput Contract..\/ 
	        Contract.Endpoint "Burn" EPInput
--- Create a blank Manager output along with its NFT (using OneShotCurrency tool)
initCDP :: forall w s. Contract.Contract w s Contract.ContractError (Value.AssetClass, Value.AssetClass)
initCDP = do
    userPubKey <- Contract.ownPubKeyHash
    mkCS   <- Contract.mapError fromCurrencyError $ Currency.currencySymbol <$> Currency.mintContract userPubKey [(managerNFTTokenName, 1)]
    let
        mAsset  = Value.assetClass mkCS managerNFTTokenName
        uAsset  = Value.assetClass (userCurrencySymbol mAsset) userTokenName
        lookup = Constraints.typedValidatorLookups (cdpInstance $ CDParams mAsset uAsset)
        val    = Value.assetClassValue mAsset 1
        constraint = Constraints.mustPayToTheScript (ManagerDatum []) val
    void $ Contract.submitTxConstraintsWith lookup constraint >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
    Contract.logInfo @String "Initiate successfully"
    return $ (mAsset, uAsset)

-- data EPInput = EPInput { epManagerT :: Value.AssetClass, epUserT :: Value.AssetClass, , epAmount :: Integer }

openCDP :: EPInput -> Contract.Contract w s Contract.ContractError ()
openCDP inp = do
      manager    <- Map.filter (isManagerOutput mtk) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
      userPubKey <- Contract.ownPubKeyHash
      if Map.null manager
         then Contract.throwError "Manager missing!"
         else do
          let
            (oref, o)  = head $ Map.toList manager
            mbListUser = getDatum @CDPDatum o
            lookup     = Constraints.typedValidatorLookups (cdpInstance $  CDParams mtk utk)
            userToken  = Value.assetClassValue (Value.assetClass (userCurrencySymbol $ mtk) userTokenName) 1
            mtk        = epManagerT inp
            utk        = epUserT inp
          case mbListUser of
            Nothing -> Contract.throwError "PubKey list missing"
            Just listUser -> do
            		   void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                  	    where
                  	      mngDatum    = ManagerDatum (userPubKey :(pkhList listUser))
                  	      lookup      = Constraints.typedValidatorLookups (cdpInstance $ CDParams mtk utk)
                  	                 <> Constraints.unspentOutputs (Map.fromList [(oref, o)])
                  	                 <> Constraints.otherScript (cdpValidator $ CDParams mtk utk)
                  	                 <> Constraints.mintingPolicy (userMintingPolicy $ mtk)
                   	      constraints = Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData (XOpen userPubKey))
                             	        <> Constraints.mustPayToTheScript mngDatum (Ada.lovelaceValueOf 0 <> getValue o)
  	                        	        <> Constraints.mustPayToTheScript (UserDatum userPubKey 0 0) (Ada.lovelaceValueOf 0 <> userToken)
  	                        	        <> Constraints.mustMintValue userToken
  	  where (mtk,utk) = (epManagerT inp, epUserT inp)                      	        
        
depositCDP :: EPInput -> Contract.Contract w s Contract.ContractError ()
depositCDP inp = do
    userPubKey   <- Contract.ownPubKeyHash
    manager      <- Map.filter (isManagerOutput mtk) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    myCollateral <- Map.filter (isUserCollateralOutput utk userPubKey) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    if Map.null manager
      then Contract.throwError "Please open a CDP in advance"
      else do
        let
    	  (mngOref, mngO) = head $ Map.toList manager
          listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
        case Map.null myCollateral of
            True -> Contract.throwError "Please open a CDP in advance, lack collateral fund"
            False -> do
                void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                    where
                        lookup = Constraints.typedValidatorLookups (cdpInstance $ CDParams mtk utk)
                                <> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                                <> Constraints.otherScript (cdpValidator $ CDParams mtk utk)
                        constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData (XDeposit userPubKey dp_amount)) 
                                <> Constraints.mustPayToTheScript newUserDat (Ada.lovelaceValueOf dp_amount <> getValue myO)
                        (myOref, myO)  = head $ Map.toList myCollateral
                        userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
                        newUserDat = (UserDatum userPubKey (dp_amount+(myLockedAda userDat)) (myMintedToken userDat))
    where (mtk,utk,dp_amount) = (epManagerT inp, epUserT inp, epAmount inp)

withdrawCDP :: EPInput -> Contract.Contract w s Contract.ContractError ()
withdrawCDP inp = do
    userPubKey   <- Contract.ownPubKeyHash
    manager      <- Map.filter (isManagerOutput mtk) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    myCollateral <- Map.filter (isUserCollateralOutput utk userPubKey) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    if Map.null manager
        then Contract.throwError "Please open a CDP in advance"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
         case Map.null myCollateral of
            True -> Contract.throwError "Please open a CDP in advance, lack collateral fund@@@"
            False -> do
                void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                    where
                        lookup 	= Constraints.typedValidatorLookups (cdpInstance $ CDParams mtk utk)
                                	<> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                                	<> Constraints.otherScript (cdpValidator $ CDParams mtk utk)
                        constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData (XWithdraw userPubKey wd_amount))
                                    <> Constraints.mustPayToTheScript newUserDat (Ada.lovelaceValueOf (-wd_amount) <> getValue myO)
                        (myOref, myO)   = head $ Map.toList myCollateral
                        userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
                        leftover = (myLockedAda userDat) - wd_amount
                        newUserDat = (UserDatum userPubKey leftover (myMintedToken userDat))
                        
    where (mtk,utk, wd_amount) = (epManagerT inp, epUserT inp, epAmount inp)                                

mintCDP :: EPInput -> Contract.Contract w s Contract.ContractError ()
mintCDP inp = do
    userPubKey   <- Contract.ownPubKeyHash
    manager      <- Map.filter (isManagerOutput mtk) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    myCollateral <- Map.filter (isUserCollateralOutput utk userPubKey) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    if Map.null manager
        then Contract.throwError "Please open a CDP in advance"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
         case Map.null myCollateral of
            True -> Contract.throwError "Please open a CDP in advance, lack collateral fund"
            False -> do
                void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                    where
                        lookup = Constraints.typedValidatorLookups (cdpInstance $ CDParams mtk utk)
                               <> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                               <> Constraints.otherScript (cdpValidator $ CDParams mtk utk)
                               <> Constraints.mintingPolicy (mintingPolicy $ utk)
                                	    
                        val    = Value.assetClassValue (Value.assetClass (myCurrencySymbol utk) myTokenName) mint_amount
                                
                        constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData (XMint userPubKey mint_amount))
                               <> Constraints.mustPayToTheScript newUserDat (getValue myO)
                               <> Constraints.mustMintValue val
                        (myOref, myO)   = head $ Map.toList myCollateral
                        userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
                        newUserDat = UserDatum userPubKey (myLockedAda userDat) (myMintedToken userDat + mint_amount)
    where (mtk,utk, mint_amount) = (epManagerT inp, epUserT inp, epAmount inp)

burnCDP :: EPInput -> Contract.Contract w s Contract.ContractError ()
burnCDP inp = do
    userPubKey   <- Contract.ownPubKeyHash
    manager      <- Map.filter (isManagerOutput mtk) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    myCollateral <- Map.filter (isUserCollateralOutput utk userPubKey) <$> Contract.utxosAt (cdpAddress $ CDParams mtk utk)
    if Map.null manager
        then Contract.throwError "Please open a CDP in advance"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
         case Map.null myCollateral of
            True -> Contract.throwError "Please open a CDP in advance, lack collateral fund"
            False -> do
                void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                    where
                        lookup = Constraints.typedValidatorLookups (cdpInstance $ CDParams mtk utk)
                                <> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                                <> Constraints.otherScript (cdpValidator $ CDParams mtk utk)
                                <> Constraints.mintingPolicy (mintingPolicy $ utk)
                                	    
                        val    = Value.assetClassValue (Value.assetClass (myCurrencySymbol utk)  myTokenName) (-burn_amount)
                                
                        constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData (XBurn userPubKey burn_amount))
                                <> Constraints.mustPayToTheScript newUserDat (getValue myO)
                                <> Constraints.mustMintValue val
                        (myOref, myO)   = head $ Map.toList myCollateral
                        userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
                        newUserDat = (UserDatum userPubKey (myLockedAda userDat) ((myMintedToken userDat) - burn_amount))
    where (mtk,utk, burn_amount) = (epManagerT inp, epUserT inp, epAmount inp)             
-- -}
fromCurrencyError :: Currency.CurrencyError -> Contract.ContractError
fromCurrencyError = \case
  (Currency.CurContractError e) -> e
  
initEndpoint :: Contract.Contract (Last (Value.AssetClass, Value.AssetClass)) InitSchema Contract.ContractError ()
initEndpoint = Contract.selectList [init] <> initEndpoint
    where
        init = Contract.endpoint @"Init" $ \_ -> Contract.handleError Contract.logError $ initCDP >>= Contract.tell . Last. Just

cdpEndpoints :: Contract.Contract EPInput CDPSchema Contract.ContractError ()
cdpEndpoints = Contract.selectList [open, deposit, withdraw, mint, burn] >> cdpEndpoints
    where  
        open = Contract.endpoint @"Open" $ \p -> Contract.handleError Contract.logError $ openCDP p
        deposit = Contract.endpoint @"Deposit" $ \amt -> Contract.handleError Contract.logError $ depositCDP amt
        withdraw = Contract.endpoint @"Withdraw" $ \amt -> Contract.handleError Contract.logError $ withdrawCDP amt
        mint = Contract.endpoint @"Mint" $ \amt -> Contract.handleError Contract.logError $ mintCDP amt
        burn = Contract.endpoint @"Burn" $ \amt -> Contract.handleError Contract.logError $ burnCDP amt

main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  w1'  <- Trace.activateContractWallet (knownWallet 1) initEndpoint
  w1   <- Trace.activateContractWallet (knownWallet 1) cdpEndpoints
  w2   <- Trace.activateContractWallet (knownWallet 2) cdpEndpoints
  -- Endpoint to init output.
  Trace.callEndpoint @"Init" w1' ()
  void $ Trace.waitNSlots 1
  
  pr  <- getParam w1'
  let para = EPInput (fst pr) (snd pr)
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Open" w1 $ para 0
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Open" w2 $ para 0
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Deposit" w1 $ para 1000000
  void $ Trace.waitNSlots 1
  
--  Trace.callEndpoint @"Deposit" w1 $ para 5030000
--  void $ Trace.waitNSlots 1

  Trace.callEndpoint @"Withdraw" w1 $ para 1000000
  void $ Trace.waitNSlots 1
  return() 
  where
    getParam :: Trace.ContractHandle (Last (Value.AssetClass, Value.AssetClass)) InitSchema Contract.ContractError -> Trace.EmulatorTrace (Value.AssetClass, Value.AssetClass)
    getParam h = do
      Trace.observableState h >>= \case
        Last (Just (p,p1)) -> return (p,p1)
        Last _        -> Trace.waitNSlots 1 >> getParam h
