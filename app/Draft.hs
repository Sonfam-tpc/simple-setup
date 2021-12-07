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
import Data.Either.Combinators (rightToMaybe)
import Control.Lens (preview)

data CDPAction = Xopen | XDeposit | XWithdraw | XMint | XBurn
	deriving Show

PlutusTx.unstableMakeIsData ''CDPAction
PlutusTx.makeLift ''CDPAction

data CDP

instance TScripts.ValidatorTypes CDP where
    type DatumType CDP = ManagerDatum
    type RedeemerType CDP = CDPAction

data ManagerDatum = ManagerDatum {pkhList :: [Ledger.PubKeyHash] } deriving Show

PlutusTx.unstableMakeIsData ''ManagerDatum
PlutusTx.makeLift ''ManagerDatum

{-# INLINEABLE combinedValidator #-}
combinedValidator :: ManagerDatum -> CDPAction -> Ledger.ScriptContext -> Bool
combinedValidator _ opts _ = case opts of
	Xopen -> True
	XDeposit -> True
	XWithdraw -> True
	XMint -> True
	XBurn -> True

cdpInstance :: TScripts.TypedValidator CDP
cdpInstance =
  TScripts.mkTypedValidator @CDP
    $$(PlutusTx.compile [||combinedValidator||])
    $$(PlutusTx.compile [||wrap||])
  where
    wrap = TScripts.wrapValidator @ManagerDatum @CDPAction

cdpValidator :: TScripts.Validator
cdpValidator = TScripts.validatorScript cdpInstance

cdpValidatorHash :: Ledger.ValidatorHash
cdpValidatorHash = TScripts.validatorHash cdpInstance

cdpAddress :: Ledger.Address
cdpAddress = Ledger.scriptAddress cdpValidator



mkOpen :: () -> () -> Ledger.ScriptContext -> Bool
mkOpen _ _ _ = True

mkDeposit :: () -> () -> Ledger.ScriptContext -> Bool
mkDeposit _ _ _ = True

data InitParams = InitParams { iPubKeyHash :: Ledger.PubKeyHash }
data OpenParams = OpenParams { oPubKeyHash :: Ledger.PubKeyHash} -- ownPubKey no longer exist
data DepositParams = DepositParams { dPubKeyHash :: Ledger.PubKeyHash, dAmount :: Integer }

type CDPSchema = Contract.Endpoint "Init" InitParams Contract..\/ 
	        Contract.Endpoint "Open" OpenParams Contract..\/
	        Contract.Endpoint "Deposit" DepositParams Contract..\/ 
	        Contract.Endpoint "Withdraw" () Contract..\/ 
	        Contract.Endpoint "Mint" () Contract..\/ 
	        Contract.Endpoint "Burn" ()
	        
--- Create a black Manager output
initCDP ::Contract.Contract w s Contract.ContractError ()
initCDP = do
    let 
       managerDatum = ManagerDatum []
       constraints = Constraints.mustPayToTheScript managerDatum $ (Ada.lovelaceValueOf 0)
       lookups = Constraints.typedValidatorLookups cdpInstance
    Contract.submitTxConstraintsWith lookups constraints >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId -- need to change validator Datum to run this - nevermind
    Contract.logInfo @String "Iniate PubKey list complete"

openCDP :: OpenParams -> Contract.Contract w s Contract.ContractError ()
openCDP op = do
      manager <- Map.filter isManagerOutput <$> Contract.utxosAt cdpAddress
      user_pubKey <- Contract.ownPubKeyHash
      if Map.null manager
         then Contract.logInfo @String $ "Manager missing!"
         else do
          let
            (oref, o) = head $ Map.toList manager
            mbListUsr = getDatum @ManagerDatum o
            lookup = Constraints.typedValidatorLookups cdpInstance
--            tx = Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData XDeposit)
          case mbListUsr of
            Nothing -> Contract.throwError "PubKey list missing"
            Just listUsr -> if user_pubKey `elem` (pkhList listUsr) then openAlready else do
            		   void $ Contract.submitTxConstraintsWith lookup sptx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
            		   void $ Contract.submitTxConstraintsWith lookup paytx >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
                  	    where
                  	      newDatum    = Scripts.Datum $ PlutusTx.toBuiltinData $ ManagerDatum $ ((pkhList listUsr) ++ [user_pubKey])
                  	      lookup      = Constraints.typedValidatorLookups cdpInstance
                  	      sptx        = Constraints.mustSpendScriptOutput oref (Scripts.Redeemer $ PlutusTx.toBuiltinData XDeposit)
                  	      paytx       = Constraints.mustPayToOtherScript cdpValidatorHash newDatum $ (Ada.lovelaceValueOf 0)    
                  	      openAlready = Contract.logInfo @String "You already opened!"
   where
      isManagerOutput :: Ledger.ChainIndexTxOut -> Bool
      isManagerOutput _ = True
      


depositCDP :: DepositParams -> Contract.Contract w s Contract.ContractError ()
depositCDP dp = do
     utxos <- Map.filter isUserDepositOutput <$> Contract.utxosAt cdpAddress
     let
       amount = dAmount dp
       user_pubKey = dPubKeyHash dp
       
       constraints = Constraints.mustPayToTheScript (ManagerDatum []) $ Ada.lovelaceValueOf amount -- actually not, it will be some UtxoDatum
       lookups = Constraints.typedValidatorLookups cdpInstance

     Contract.submitTxConstraintsWith lookups constraints >>= Contract.awaitTxConfirmed . Ledger.getCardanoTxId
     Contract.logInfo @String $ "How to make use of the prev utxos at script outputs?" 
  where
     isUserDepositOutput :: Ledger.ChainIndexTxOut -> Bool -- get the former utxo as the current input
     isUserDepositOutput _ = True

       
getDatum :: PlutusTx.FromData b => Ledger.ChainIndexTxOut -> Maybe b
getDatum o = preview Ledger.ciTxOutDatum o >>= rightToMaybe >>= (PlutusTx.fromBuiltinData.Ledger.getDatum)

