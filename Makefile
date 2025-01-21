PATH := ~/.solc-select/artifacts/:~/.solc-select/artifacts/solc-0.8.21:$(PATH)
certora-usdc-vault    :; PATH=${PATH} certoraRun UsdcVault.conf$(if $(rule), --rule $(rule),)$(if $(results), --wait_for_results all,)
certora-usdc-vault-l2 :; PATH=${PATH} certoraRun UsdcVaultL2.conf$(if $(rule), --rule $(rule),)$(if $(results), --wait_for_results all,)
