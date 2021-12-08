{-# LANGUAGE DataKinds #-}
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

module Specification where

import Control.Monad (void)
import qualified Data.Map as Map
import qualified Ledger
import qualified Ledger.Ada as Ada
import qualified Ledger.Constraints as Constraints
import qualified Ledger.Scripts as Scripts
import qualified Ledger.Typed.Scripts as TScripts
import qualified Ledger.Value as Value
import qualified Plutus.Contract as Contract
import qualified Plutus.Trace.Emulator as Trace
import qualified PlutusTx
import Wallet.Emulator (knownWallet)
import Prelude
import Control.Lens (preview, view)
import Data.Either.Combinators (rightToMaybe)
import Data.Maybe (fromMaybe)
import Text.Printf (printf)

data CDPAction = XOpen | XDeposit | XWithdraw | XMint | XBurn
	deriving Show

PlutusTx.unstableMakeIsData ''CDPAction
PlutusTx.makeLift ''CDPAction

data CDP

instance TScripts.ValidatorTypes CDP where
    type DatumType CDP = CDPDatum
    type RedeemerType CDP = CDPAction

data CDPDatum = ManagerDatum {pkhList :: [Ledger.PubKeyHash]} |
                UserDatum {myPubKey :: Ledger.PubKeyHash, myLockedAda :: Integer, myMintedToken :: Integer}
		  deriving Show

PlutusTx.unstableMakeIsData ''CDPDatum
PlutusTx.makeLift ''CDPDatum

getDatum :: PlutusTx.FromData b => Ledger.ChainIndexTxOut -> Maybe b
getDatum o = preview Ledger.ciTxOutDatum o >>= rightToMaybe >>= (PlutusTx.fromBuiltinData.Ledger.getDatum)

getValue :: Ledger.ChainIndexTxOut -> Ledger.Value
getValue = view Ledger.ciTxOutValue

{-# INLINEABLE cdpValidator #-}
mkValidator :: CDPDatum -> CDPAction -> Ledger.ScriptContext -> Bool
mkValidator _ opts _ = case opts of
	XOpen -> True
	XDeposit -> True
	XWithdraw -> True
	XMint -> True
	XBurn -> True

cdpInstance :: TScripts.TypedValidator CDP
cdpInstance =
  TScripts.mkTypedValidator @CDP
    $$(PlutusTx.compile [||mkValidator||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TScripts.wrapValidator @CDPDatum @CDPAction

cdpValidator :: TScripts.Validator
cdpValidator = TScripts.validatorScript cdpInstance

cdpValidatorHash :: Ledger.ValidatorHash
cdpValidatorHash = TScripts.validatorHash cdpInstance

cdpAddress :: Ledger.Address
cdpAddress = Ledger.scriptAddress cdpValidator

{-# INLINEABLE mkPolicy #-}
mkPolicy :: () -> Ledger.ScriptContext -> Bool
mkPolicy _ _ = True

mintingPolicy :: TScripts.MintingPolicy
mintingPolicy =
  Ledger.mkMintingPolicyScript
    $$(PlutusTx.compile [||TScripts.wrapMintingPolicy mkPolicy||])

mintingPolicyHash :: Scripts.MintingPolicyHash
mintingPolicyHash = Scripts.mintingPolicyHash mintingPolicy

myCurrencySymbol :: Value.CurrencySymbol
myCurrencySymbol = Value.mpsSymbol mintingPolicyHash

myTokenName :: Value.TokenName
myTokenName = "iTSLA"

type CDPSchema = Contract.Endpoint "Init" () Contract..\/ 
	        Contract.Endpoint "Open" () Contract..\/
	        Contract.Endpoint "Deposit" Integer Contract..\/ 
	        Contract.Endpoint "Withdraw" Integer Contract..\/ 
	        Contract.Endpoint "Mint" Integer Contract..\/ 
	        Contract.Endpoint "Burn" Integer
	        
--- Create a blank Manager output
initCDP ::Contract.Contract w s Contract.ContractError ()
initCDP = do
    let 
       managerDatum = ManagerDatum []
       constraints = Constraints.mustPayToTheScript managerDatum $ (Ada.lovelaceValueOf 1)
       lookups = Constraints.typedValidatorLookups cdpInstance
    Contract.submitTxConstraintsWith lookups constraints >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
    Contract.logInfo @String "Initiate PubKey list complete"

openCDP :: Contract.Contract w s Contract.ContractError ()
openCDP = do
      manager    <- Map.filter isManagerOutput <$> Contract.utxosAt cdpAddress
      userPubKey <- Contract.ownPubKeyHash
      if Map.null manager
         then Contract.throwError "Manager missing!"
         else do
          let
            (oref, o) = head $ Map.toList manager
            mbListUser = getDatum @CDPDatum o
            lookup = Constraints.typedValidatorLookups cdpInstance
          case mbListUser of
            Nothing -> Contract.throwError "PubKey list missing"
            Just listUser -> if userPubKey `elem` (pkhList listUser) then openAlready else do
            		   void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                  	    where
                  	      mngDatum    = ManagerDatum ((pkhList listUser) ++ [userPubKey])
                  	      lookup      = Constraints.typedValidatorLookups cdpInstance
                  	                 <> Constraints.unspentOutputs (Map.fromList [(oref, o)])
                  	                 <> Constraints.otherScript cdpValidator
                   	      constraints = Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData XOpen)
                             	        <> Constraints.mustPayToTheScript mngDatum (Ada.lovelaceValueOf 0)
  	                        	        <> Constraints.mustPayToTheScript (UserDatum userPubKey 0 0) (Ada.lovelaceValueOf 0) 
                  	      openAlready = Contract.logInfo @String "You already opened!"
   where
     isManagerOutput :: Ledger.ChainIndexTxOut -> Bool
     isManagerOutput inp = case getDatum @CDPDatum inp of
        Just (ManagerDatum _) -> True
        _                     -> False
      
depositCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
depositCDP dp_amount = do
    manager      <- Map.filter isManagerOutput <$> Contract.utxosAt cdpAddress
    myCollateral <- Map.filter isUserCollateralOutput <$> Contract.utxosAt cdpAddress
    userPubKey   <- Contract.ownPubKeyHash
    if Map.null myCollateral
        then Contract.throwError "Please open a CDP in advance, lack collateral fund"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            (myOref, myO)   = head $ Map.toList myCollateral
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
            userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
            
            cur_AdaAmount = myLockedAda userDat
            cur_MintedToken = myMintedToken userDat
            newUserDat = (UserDatum userPubKey (dp_amount+cur_AdaAmount) cur_MintedToken)   
         case userPubKey `elem` listUser of
            False -> Contract.logInfo @String "Please open a CDP in advance, lack manager output"
            True -> case dp_amount <= 0 of
                True  -> Contract.logInfo @String "Please deposit a positve asset"
                False -> do
                    void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                      where
                        lookup      = Constraints.typedValidatorLookups cdpInstance
                  	                <> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                  	                <> Constraints.otherScript cdpValidator
                        constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData XDeposit)
                                    <> Constraints.mustPayToTheScript newUserDat (Ada.lovelaceValueOf (dp_amount + cur_AdaAmount))
    where
     isUserCollateralOutput :: Ledger.ChainIndexTxOut -> Bool -- get the former utxo as the current input (use PubKey + authToken)
     isUserCollateralOutput inp = case getDatum @CDPDatum inp of
        Just (UserDatum _ _ _) -> True
        _                      -> False
     
     isManagerOutput :: Ledger.ChainIndexTxOut -> Bool
     isManagerOutput inp = case getDatum @CDPDatum inp of
        Just (ManagerDatum _) -> True
        _                     -> False

withdrawCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
withdrawCDP wd_amount = do
    manager      <- Map.filter isManagerOutput <$> Contract.utxosAt cdpAddress
    myCollateral <- Map.filter isUserCollateralOutput <$> Contract.utxosAt cdpAddress
    userPubKey   <- Contract.ownPubKeyHash
    if Map.null myCollateral
        then Contract.logInfo @String "Please open a CDP in advance, lack collateral fund"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            (myOref, myO)   = head $ Map.toList myCollateral
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
            userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
            
            cur_AdaAmount = myLockedAda userDat
            leftover = cur_AdaAmount - wd_amount
            cur_MintedToken = myMintedToken userDat
            
            checkRatio :: Bool
            checkRatio = 13 * leftover * 10^11 >= 15 * 70967 * 10^9 * cur_MintedToken
            
            newUserDat = (UserDatum userPubKey leftover cur_MintedToken)
         case userPubKey `elem` listUser of
            False -> Contract.logInfo @String "Please open a CDP in advance, lack manager output"
            True -> case leftover < 0 of
                True  -> Contract.logInfo @String "Insufficient fund"
                False -> if not checkRatio then Contract.logInfo @String "Your withdrawl breaks the collateral ratio" else do
                    void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                      where
                        lookup 	= Constraints.typedValidatorLookups cdpInstance
                                	<> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                                	<> Constraints.otherScript cdpValidator
                        constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData XWithdraw)
                                    <> Constraints.mustPayToTheScript newUserDat (Ada.lovelaceValueOf leftover)
    where
     isUserCollateralOutput :: Ledger.ChainIndexTxOut -> Bool -- get the former utxo as the current input (use PubKey + authToken)
     isUserCollateralOutput inp = case getDatum @CDPDatum inp of
        Just (UserDatum _ _ _) -> True
        _                      -> False
     
     isManagerOutput :: Ledger.ChainIndexTxOut -> Bool
     isManagerOutput inp = case getDatum @CDPDatum inp of
        Just (ManagerDatum _) -> True
        _                     -> False


mintCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
mintCDP mint_amount = do
    manager      <- Map.filter isManagerOutput <$> Contract.utxosAt cdpAddress
    myCollateral <- Map.filter isUserCollateralOutput <$> Contract.utxosAt cdpAddress
    userPubKey   <- Contract.ownPubKeyHash
    if Map.null myCollateral
        then Contract.logInfo @String "Please open a CDP in advance, lack collateral fund"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            (myOref, myO)   = head $ Map.toList myCollateral
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
            userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)
            
            cur_AdaAmount = myLockedAda userDat
            cur_MintedToken = myMintedToken userDat
            upd_MintedToken = cur_MintedToken + mint_amount
            newUserDat = (UserDatum userPubKey cur_AdaAmount upd_MintedToken)
            
            checkRatio :: Bool -- create const value for some random number
            checkRatio = 13 * cur_AdaAmount * 10^11 >= 15 * 70967 * 10^9 * upd_MintedToken
            
            maxAmountMinted :: Integer --- assume that we can only mint a postive integer amount
            maxAmountMinted = (13 * cur_AdaAmount * 10^11) `div` (15 * 70967 * 10^9)
         case userPubKey `elem` listUser of
            False -> Contract.logInfo @String "Please open a CDP in advance, lack manager output"
            True  -> case mint_amount > 0 of
                False -> Contract.logInfo @String "Please mint a positve amount of TSLA"
                True  -> case checkRatio of
                    False -> Contract.logInfo @String $ printf "Collatertal ratio broke, please only mint %d lovelace maximum" maxAmountMinted
                    True  -> do
                        void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                            where
                                lookup = Constraints.typedValidatorLookups cdpInstance
                                        <> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                                	    <> Constraints.otherScript cdpValidator
                                	    <> Constraints.mintingPolicy mintingPolicy
                                	    
                                val    = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) mint_amount
                                
                                constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData XMint)
                                            <> Constraints.mustPayToTheScript newUserDat (Ada.lovelaceValueOf cur_AdaAmount)
                                            <> Constraints.mustMintValue val
    where
     isUserCollateralOutput :: Ledger.ChainIndexTxOut -> Bool -- get the former utxo as the current input (use PubKey + authToken)
     isUserCollateralOutput inp = case getDatum @CDPDatum inp of
        Just (UserDatum _ _ _) -> True
        _                      -> False
     
     isManagerOutput :: Ledger.ChainIndexTxOut -> Bool
     isManagerOutput inp = case getDatum @CDPDatum inp of
        Just (ManagerDatum _) -> True
        _                     -> False

burnCDP :: Integer -> Contract.Contract w s Contract.ContractError ()
burnCDP burn_amount = do
    manager      <- Map.filter isManagerOutput <$> Contract.utxosAt cdpAddress
    myCollateral <- Map.filter isUserCollateralOutput <$> Contract.utxosAt cdpAddress
    userPubKey   <- Contract.ownPubKeyHash
    if Map.null myCollateral
        then Contract.logInfo @String "Please open a CDP in advance, lack collateral fund"
        else do
         let
            (mngOref, mngO) = head $ Map.toList manager
            (myOref, myO)   = head $ Map.toList myCollateral
            listUser = pkhList $ fromMaybe (ManagerDatum []) (getDatum @CDPDatum mngO)
            userDat  = fromMaybe (UserDatum userPubKey 0 0) (getDatum @CDPDatum myO)

            cur_AdaAmount = myLockedAda userDat
            cur_MintedToken = myMintedToken userDat
            upd_MintedToken = cur_MintedToken - burn_amount
            newUserDat = (UserDatum userPubKey cur_AdaAmount upd_MintedToken)
         case userPubKey `elem` listUser of
            False -> Contract.logInfo @String "Please open a CDP in advance, lack manager output"
            True  -> case upd_MintedToken > 0 of
                False -> Contract.logInfo @String $ printf "Burn exceeds your balance, please burn under %d TSLA" cur_MintedToken
                True  -> do
                            void $ Contract.submitTxConstraintsWith lookup constraints >>= Contract.awaitTxConfirmed. Ledger.getCardanoTxId
                                where
                                    lookup = Constraints.typedValidatorLookups cdpInstance
                                        <> Constraints.unspentOutputs (Map.fromList [(myOref, myO)])
                                	    <> Constraints.otherScript cdpValidator
                                	    <> Constraints.mintingPolicy mintingPolicy
                                	    
                                    val    = Value.assetClassValue (Value.assetClass myCurrencySymbol myTokenName) (-burn_amount)
                                
                                    constraints = Constraints.mustSpendScriptOutput myOref (Scripts.Redeemer $ PlutusTx.toBuiltinData XBurn)
                                            <> Constraints.mustPayToTheScript newUserDat (Ada.lovelaceValueOf cur_AdaAmount)
                                            <> Constraints.mustMintValue val
    where
     isUserCollateralOutput :: Ledger.ChainIndexTxOut -> Bool -- get the former utxo as the current input (use PubKey + authToken)
     isUserCollateralOutput inp = case getDatum @CDPDatum inp of
        Just (UserDatum _ _ _) -> True
        _                      -> False
     
     isManagerOutput :: Ledger.ChainIndexTxOut -> Bool
     isManagerOutput inp = case getDatum @CDPDatum inp of
        Just (ManagerDatum _) -> True
        _                     -> False
cdpEndpoints :: Contract.Contract () CDPSchema Contract.ContractError ()
cdpEndpoints = Contract.selectList [init, open, deposit, withdraw, mint, burn] >> cdpEndpoints
    where
        init = Contract.endpoint @"Init" $ \_ -> Contract.handleError Contract.logError $ initCDP  
        open = Contract.endpoint @"Open" $ \_ -> Contract.handleError Contract.logError openCDP
        deposit = Contract.endpoint @"Deposit" $ \amt -> Contract.handleError Contract.logError $ depositCDP amt
        withdraw = Contract.endpoint @"Withdraw" $ \amt -> Contract.handleError Contract.logError $ withdrawCDP amt
        mint = Contract.endpoint @"Mint" $ \amt -> Contract.handleError Contract.logError $ mintCDP amt
        burn = Contract.endpoint @"Burn" $ \amt -> Contract.handleError Contract.logError $ burnCDP amt

main :: IO ()
main = Trace.runEmulatorTraceIO $ do
  -- activate contract from wallet 1. We got function testEndpoints so that we only need to activate all the endpoints once for each wallet.
  hdl  <- Trace.activateContractWallet (knownWallet 1) cdpEndpoints
  w2  <- Trace.activateContractWallet (knownWallet 2) cdpEndpoints
  -- Endpoint to init output.
  Trace.callEndpoint @"Init" hdl ()
  void $ Trace.waitNSlots 1

  -- Endpoint to open. This case using the activation from wallet 1 but you can try to activate from another wallet.
  Trace.callEndpoint @"Open" hdl ()
  Trace.callEndpoint @"Open" w2  ()
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Deposit" hdl 10000000
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Deposit" w2 9000000
  void $ Trace.waitNSlots 1
  
  Trace.callEndpoint @"Withdraw" hdl 1290000
  void $ Trace.waitNSlots 1
