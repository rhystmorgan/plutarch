-- These Validators solve the cyclical dependancy

data PMintAction (s :: S) = PMint | PBurn
  deriving stock (Generic, Enum, Bounded)
  deriving anyclass (PlutusType, PIsData, PEq, PShow)

instance DerivePlutusType PMintAction where
  type DPTStrat _ = PlutusTypeEnumData 

instance PTryFrom PData PMintAction
instance PTryFrom PData (PAsData PMintAction)

--                   --
-- 2 Script Solution --
--                   --

pValidatorMint :: Term s (PData PValidatorHash 
  :--> PAsData TxOutRef 
  :--> PMintAction  
  :--> PScriptContext 
  :--> PUnit
  )
pValidateMint = phoistAcyclic $ plam $ \vh oref ma ctx -> unTermCont $ do
    ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
    infoF <- pletFieldsC @'["mint", "inputs", "outputs", "signatories"] ctxF.txInfo
    PMinting ((pfield @"_0" ) -> ownRef) <- pmatchC ctxF.purpose

    pure $ 
      pif 
        (pmatch redeemer $ \case
          PMint -> 
            minted #== 1
              #&& burned #== 0
              #&& pany @PBuiltinList
                # plam (\txo -> pletFields @'["value", "address", "datum"] $ \txoF -> 
                  pmatch (pfield @"credential" # txoF.address) $ \case 
                    PPubKeyCredential _ -> perror
                    PScriptCredential vh -> pvalueOf # txoF.value #== [("", "", 2_000_000), (ownCS, "", 1)]
                      #&& ptryFrom @PMiltiSigDatum txoF.datum 
                )
          PBurn -> minted #== 0 #&& burned #== (-1) 
        )
        (pconstant ())
        perror

pProjectTokenPolicy :: Term s (PValidatorHash 
  :--> PCurrencySymbol 
  :--> PMintAction 
  :--> PScriptContext 
  :--> PUnit
  )
pProjectTokenPolicy = phoistAcyclic $ plam $ \vh cs ma ctx -> unTermCont $ do
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
  infoF <- pletFieldsC @'["mint", "inputs", "outputs", "signatories"] ctxF.txInfo
  txInF <- pfield @"resolved" ()
  PMinting ((pfield @"_0" ) -> ownRef) <- pmatchC ctxF.purpose

  pure $ 
    pif 
      (pmatch redeemer $ \case
        PMint -> 
          minted #== 1
            #&& burned #== 0
            #&& pany @PBuiltinList
              # plam (\txo -> pletFields @'["value", "address", "datum"] $ \txoF ->
                pmatch (pfield @"credential" # txoF.address) $ \case
                  PPubKeyCredential _ -> perror
                  PScriptCredential vh -> pvalueOf # txoF.value #== [("", "", 2_000_000), (cs, "", 1)]
                    #&& ptryFrom @PMultiSigDatum txoF.datum
                )
        PBurn -> minted #== 0 #&& burned #== (-1)
      )
      (pconstant ())
      perror

--                   --
-- 1 Script Solution --
--                   --

pMintingPolicy :: Term s (PValidatorHash
  :--> PMintAction
  :--> PScriptContext
  :--> PUnit
  )
pMintingPolicy = phoistAcyclic $ plam $ \vh ma ctx -> unTermCont $ do
  ctxF <- pletFieldsC @'["txInfo", "purpose"] ctx
  infoF <- pletFieldsC @'["mints", "inputs", "outputs", "signatories"] ctxF.txInfo
  PMinting ((pfield @"_0") -> ownRef) <- pmatchC ctxF.purpose

  pure $ 
    pif
      (pmatch redeemer $ \case
        PMint -> 
          minted #== 1
            #&& burned #== 0
            #&& plength (pfilter 
              (\o -> (case 
                Address (PScriptCredential vh) -> True
                _ -> False
              ))
              infoF.outputs) #== 1
            #&& pany @PBuiltinList
              # plam
        PBurn -> minted #== 0 #&& burned #== (-1)
      )
      (pconstant ())
      perror

