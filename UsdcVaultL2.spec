// UsdcVaultL2.spec

using Psm3Mock as psm;
using SUsdsMock as susds;
using UsdcMock as usdc;
using UsdsMock as usds;
using RateProviderMock as rateProvider;
using SignerMock as signer;
using Auxiliar as aux;

methods {
    // storage variables
    function wards(address) external returns (uint256) envfree;
    function totalSupply() external returns (uint256) envfree;
    function balanceOf(address) external returns (uint256) envfree;
    function allowance(address, address) external returns (uint256) envfree;
    function nonces(address) external returns (uint256) envfree;
    // immutables
    function usdc() external returns (address) envfree;
    //
    function DOMAIN_SEPARATOR() external returns (bytes32) envfree;
    function PERMIT_TYPEHASH() external returns (bytes32) envfree;
    //
    function psm.pocket() external returns (address) envfree;
    function susds.allowance(address, address) external returns (uint256) envfree;
    function susds.balanceOf(address) external returns (uint256) envfree;
    function susds.totalSupply() external returns (uint256) envfree;
    function usdc.allowance(address, address) external returns (uint256) envfree;
    function usdc.balanceOf(address) external returns (uint256) envfree;
    function usdc.totalSupply() external returns (uint256) envfree;
    function usds.balanceOf(address) external returns (uint256) envfree;
    function aux.call_ecrecover(bytes32, uint8, bytes32, bytes32) external returns (address) envfree;
    function aux.computeDigestForToken(bytes32, bytes32, address, address, uint256, uint256, uint256) external returns (bytes32) envfree;
    function aux.signatureToVRS(bytes) external returns (uint8, bytes32, bytes32) envfree;
    function aux.VRSToSignature(uint8, bytes32, bytes32) external returns (bytes) envfree;
    function aux.size(bytes) external returns (uint256) envfree;
    function rateProvider.getConversionRate() external returns (uint256) envfree;
    //
    function _.transfer(address,uint256) external => DISPATCHER(true);
    function _.transferFrom(address,address,uint256) external => DISPATCHER(true);
    function _.isValidSignature(bytes32, bytes) external => DISPATCHER(true);
}

definition RAY() returns mathint = 10^27;
definition _min(mathint x, mathint y) returns mathint = x < y ? x : y;
definition defCeilDiv(mathint a, mathint b) returns mathint = b == 0 ? a / b : (a == 0 ? 0 : (a - 1) / b + 1);
definition defConvertToSUsds(mathint amount, mathint assetPrecision, bool roundUp)
returns mathint = rateProvider.getConversionRate() == 0 ? 0 :
                  !roundUp ? amount * 10^27 / rateProvider.getConversionRate() * psm._susdsPrecision / assetPrecision
                           : defCeilDiv(defCeilDiv(amount * 10^27, rateProvider.getConversionRate()) * psm._susdsPrecision, assetPrecision);
definition defConvertFromSUsds(mathint amount, mathint assetPrecision, bool roundUp)
returns mathint = !roundUp ? amount * rateProvider.getConversionRate() / 10^27 * assetPrecision / psm._susdsPrecision
                           : defCeilDiv(defCeilDiv(amount * rateProvider.getConversionRate(), 10^27) * assetPrecision, psm._susdsPrecision);
definition defConvertOneToOne(mathint amount, mathint assetPrecision, mathint convertAssetPrecision, bool roundUp)
returns mathint = !roundUp ? amount * convertAssetPrecision / assetPrecision
                           : defCeilDiv(amount * convertAssetPrecision, assetPrecision);
definition defGetSwapQuote(address asset, address quoteAsset, mathint amount, bool roundUp)
returns mathint = (asset == usdc  && quoteAsset == susds ? defConvertToSUsds(amount, psm._usdcPrecision, roundUp) : 0) +
                  (asset == susds && quoteAsset == usdc  ? defConvertFromSUsds(amount, psm._usdcPrecision, roundUp) : 0);

ghost susds_balanceSum() returns mathint {
    init_state axiom susds_balanceSum() == 0;
}
hook Sstore susds.balanceOf[KEY address a] uint256 balance (uint256 old_balance) {
    havoc susds_balanceSum assuming susds_balanceSum@new() == susds_balanceSum@old() + balance - old_balance;
}
invariant susds_balanceSum_equals_totalSupply() susds_balanceSum() == to_mathint(susds.totalSupply()) 
            filtered {
                m -> m.selector != sig:upgradeToAndCall(address, bytes).selector
            }

ghost balanceSum() returns mathint {
    init_state axiom balanceSum() == 0;
}
hook Sstore balanceOf[KEY address a] uint256 balance (uint256 old_balance) {
    havoc balanceSum assuming balanceSum@new() == balanceSum@old() + balance - old_balance && balanceSum@new() >= 0;
}
invariant balanceSum_equals_totalSupply() balanceSum() <= susds.balanceOf(currentContract) && susds.balanceOf(currentContract) + susds.balanceOf(psm) <= susds.totalSupply() && balanceSum() == to_mathint(totalSupply())
            filtered {
                m -> m.selector != sig:upgradeToAndCall(address, bytes).selector
            } {
                preserved {
                    requireInvariant susds_balanceSum_equals_totalSupply;
                }
}

rule invariant_vault_total_supply_equals_susds_balance(method f) filtered { f -> !f.isView &&
                                                                        f.selector != sig:upgradeToAndCall(address,bytes).selector } {
    env e;
    
    require totalSupply() == susds.balanceOf(currentContract);

    if (f.selector == sig:exit(uint256, address, address).selector) {
        uint256 shares;
        address receiver;
        address owner;
        require receiver != currentContract;
        exit(e, shares, receiver, owner);
    } else {
        calldataarg args;
        f(e, args);
    }

    assert totalSupply() == susds.balanceOf(currentContract), "Assert 1";
}

rule invariant_vault_usdc_and_usds_balance_is_0(method f) filtered { f -> !f.isView } {
    env e;

    address pocket = psm.pocket();
    require pocket != currentContract;
    
    require usdc.balanceOf(currentContract) == 0;
    require usds.balanceOf(currentContract) == 0;

    if (f.selector == sig:withdraw(uint256,address,address).selector) {
        uint256 assets;
        address receiver;
        address owner;
        require receiver != currentContract;
        withdraw(e, assets, receiver, owner);
    } else if (f.selector == sig:withdraw(uint256,address,address,uint256).selector) {
        uint256 assets;
        address receiver;
        address owner;
        uint256 maxShares;
        require receiver != currentContract;
        withdraw(e, assets, receiver, owner, maxShares);
    } else if (f.selector == sig:redeem(uint256,address,address).selector) {
        uint256 shares;
        address receiver;
        address owner;
        require receiver != currentContract;
        redeem(e, shares, receiver, owner);
    } else if (f.selector == sig:redeem(uint256,address,address,uint256).selector) {
        uint256 shares;
        address receiver;
        address owner;
        uint256 minAssets;
        require receiver != currentContract;
        redeem(e, shares, receiver, owner, minAssets);
    } else {
        calldataarg args;
        f(e, args);
    }

    assert usdc.balanceOf(currentContract) == 0, "Assert 1";
    assert usds.balanceOf(currentContract) == 0, "Assert 2";
}

rule invariant_maxDeposit(address anyAddr) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;
    
    address receiver;
    require receiver != 0 && receiver != currentContract;

    uint256 maxDeposit = maxDeposit(e, anyAddr);
    require maxDeposit > 0;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    // Contracts set up
    require usdc.allowance(currentContract, psm) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm) + susds.balanceOf(receiver);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= maxDeposit;
    require usdc.balanceOf(e.msg.sender) >= maxDeposit;

    // Avoid overflows
    require maxDeposit * RAY() <= max_uint256;
    require maxDeposit * RAY() / rate * psm._susdsPrecision <= max_uint256;

    deposit@withrevert(e, maxDeposit, receiver);
    bool lastRevertedValue = lastReverted;

    mathint susdsBalanceOfPSMAfter = susds.balanceOf(psm);
    mathint maxDepositAfter = maxDeposit(e, anyAddr);

    assert !lastRevertedValue, "Assert 1";
    assert susdsBalanceOfPSMAfter <= 10 * 10^12, "Assert 2";
    assert maxDepositAfter <= 10 * 10^12, "Assert 3";
}

rule invariant_maxMint(address anyAddr) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;
    
    address receiver;
    require receiver != 0 && receiver != currentContract;

    uint256 maxMint = maxMint(e, anyAddr);
    require maxMint > 0;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    // Contracts set up
    require usdc.allowance(currentContract, psm) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm) + susds.balanceOf(receiver);

    mathint assets = previewMint(e, maxMint);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid overflows
    require maxMint * rate <= max_uint256;
    require maxMint * rate / RAY() * psm._usdcPrecision <= max_uint256;

    mint@withrevert(e, maxMint, receiver);
    bool lastRevertedValue = lastReverted;

    mathint susdsBalanceOfPSMAfter = susds.balanceOf(psm);
    mathint maxMintAfter = maxMint(e, anyAddr);

    assert !lastRevertedValue, "Assert 1";
    assert susdsBalanceOfPSMAfter <= 10^12, "Assert 2";
    assert maxMintAfter == 0, "Assert 3";
}

rule invariant_maxWithdraw(address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();

    address receiver;
    require receiver != 0 && receiver != currentContract && receiver != pocket;

    uint256 maxWithdraw = maxWithdraw(e, owner);
    require maxWithdraw > 0;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require susds.allowance(currentContract, psm) == max_uint256;

    // Contract behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(pocket) + usdc.balanceOf(currentContract) + usdc.balanceOf(receiver);
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm);

    // Owner => sender allowance
    require allowance(owner, e.msg.sender) == max_uint256;

    // Avoid overflows
    require maxWithdraw * RAY() <= max_uint256;
    require defCeilDiv(maxWithdraw * RAY(), rate) * psm._susdsPrecision <= max_uint256;

    withdraw@withrevert(e, maxWithdraw, receiver, owner);
    bool lastRevertedValue = lastReverted;

    mathint maxWithdrawAfter = maxWithdraw(e, owner);

    assert !lastRevertedValue, "Assert 1";
    assert maxWithdrawAfter == 0, "Assert 2";
}

rule invariant_maxRedeem(address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();

    address receiver;
    require receiver != 0 && receiver != currentContract && receiver != pocket;

    uint256 maxRedeem = maxRedeem(e, owner);
    require maxRedeem > 0;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require susds.allowance(currentContract, psm) == max_uint256;

    // Contract behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(pocket) + usdc.balanceOf(currentContract) + usdc.balanceOf(receiver);
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm);

    // Owner => sender allowance
    require allowance(owner, e.msg.sender) == max_uint256;

    // Avoid overflows
    require maxRedeem * rate <= max_uint256;
    require maxRedeem * rate / RAY() * psm._usdcPrecision <= max_uint256;

    redeem@withrevert(e, maxRedeem, receiver, owner);
    bool lastRevertedValue = lastReverted;

    mathint maxRedeemAfter = maxRedeem(e, owner);

    assert !lastRevertedValue, "Assert 1";
    assert maxRedeemAfter <= 10^12, "Assert 2";
}

// Verify no more entry points exist
rule entryPoints(method f) filtered { f -> !f.isView } {
    env e;

    calldataarg args;
    f(e, args);

    assert f.selector == sig:initialize().selector ||
           f.selector == sig:upgradeToAndCall(address,bytes).selector ||
           f.selector == sig:rely(address).selector ||
           f.selector == sig:deny(address).selector ||
           f.selector == sig:transfer(address,uint256).selector ||
           f.selector == sig:transferFrom(address,address,uint256).selector ||
           f.selector == sig:approve(address,uint256).selector ||
           f.selector == sig:deposit(uint256,address).selector ||
           f.selector == sig:deposit(uint256,address,uint256,uint16).selector ||
           f.selector == sig:mint(uint256,address).selector ||
           f.selector == sig:mint(uint256,address,uint256,uint16).selector ||
           f.selector == sig:withdraw(uint256,address,address).selector ||
           f.selector == sig:withdraw(uint256,address,address,uint256).selector ||
           f.selector == sig:redeem(uint256,address,address).selector ||
           f.selector == sig:redeem(uint256,address,address,uint256).selector ||
           f.selector == sig:exit(uint256,address,address).selector ||
           f.selector == sig:permit(address,address,uint256,uint256,bytes).selector ||
           f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector;
}

// Verify that each storage layout is only modified in the corresponding functions
rule storageAffected(method f) filtered { f -> f.selector != sig:upgradeToAndCall(address,bytes).selector } {
    env e;

    address anyAddr;
    address anyAddr2;

    mathint wardsBefore = wards(anyAddr);
    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfBefore = balanceOf(anyAddr);
    mathint allowanceBefore = allowance(anyAddr, anyAddr2);
    mathint noncesBefore = nonces(anyAddr);

    calldataarg args;
    f(e, args);

    mathint wardsAfter = wards(anyAddr);
    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfAfter = balanceOf(anyAddr);
    mathint allowanceAfter = allowance(anyAddr, anyAddr2);
    mathint noncesAfter = nonces(anyAddr);

    assert wardsAfter != wardsBefore             => f.selector == sig:initialize().selector ||
                                                    f.selector == sig:rely(address).selector ||
                                                    f.selector == sig:deny(address).selector, "Assert 1";
    assert totalSupplyAfter != totalSupplyBefore => f.selector == sig:deposit(uint256,address).selector ||
                                                    f.selector == sig:deposit(uint256,address,uint256,uint16).selector ||
                                                    f.selector == sig:mint(uint256,address).selector ||
                                                    f.selector == sig:mint(uint256,address,uint256,uint16).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address,uint256).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address,uint256).selector ||
                                                    f.selector == sig:exit(uint256,address,address).selector, "Assert 2";
    assert balanceOfAfter != balanceOfBefore     => f.selector == sig:deposit(uint256,address).selector ||
                                                    f.selector == sig:deposit(uint256,address,uint256,uint16).selector ||
                                                    f.selector == sig:mint(uint256,address).selector ||
                                                    f.selector == sig:mint(uint256,address,uint256,uint16).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address,uint256).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address,uint256).selector ||
                                                    f.selector == sig:transfer(address,uint256).selector ||
                                                    f.selector == sig:transferFrom(address,address,uint256).selector ||
                                                    f.selector == sig:exit(uint256,address,address).selector, "Assert 3";
    assert allowanceAfter != allowanceBefore     => f.selector == sig:approve(address,uint256).selector ||
                                                    f.selector == sig:transferFrom(address,address,uint256).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address).selector ||
                                                    f.selector == sig:withdraw(uint256,address,address,uint256).selector ||
                                                    f.selector == sig:redeem(uint256,address,address).selector ||
                                                    f.selector == sig:redeem(uint256,address,address,uint256).selector ||
                                                    f.selector == sig:exit(uint256,address,address).selector ||
                                                    f.selector == sig:permit(address,address,uint256,uint256,bytes).selector ||
                                                    f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector, "Assert 4";
    assert noncesAfter != noncesBefore           => f.selector == sig:permit(address,address,uint256,uint256,bytes).selector ||
                                                    f.selector == sig:permit(address,address,uint256,uint256,uint8,bytes32,bytes32).selector, "Assert 5";
}

// Verify correct storage changes for non reverting rely
rule rely(address usr) {
    env e;

    address other;
    require other != usr;

    mathint wardsOtherBefore = wards(other);

    rely(e, usr);

    mathint wardsUsrAfter = wards(usr);
    mathint wardsOtherAfter = wards(other);

    assert wardsUsrAfter == 1, "Assert 1";
    assert wardsOtherAfter == wardsOtherBefore, "Assert 2";
}

// Verify revert rules on rely
rule rely_revert(address usr) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    rely@withrevert(e, usr);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting deny
rule deny(address usr) {
    env e;

    address other;
    require other != usr;

    mathint wardsOtherBefore = wards(other);

    deny(e, usr);

    mathint wardsUsrAfter = wards(usr);
    mathint wardsOtherAfter = wards(other);

    assert wardsUsrAfter == 0, "Assert 1";
    assert wardsOtherAfter == wardsOtherBefore, "Assert 2";
}

// Verify revert rules on deny
rule deny_revert(address usr) {
    env e;

    mathint wardsSender = wards(e.msg.sender);

    deny@withrevert(e, usr);

    bool revert1 = e.msg.value > 0;
    bool revert2 = wardsSender != 1;

    assert lastReverted <=> revert1 || revert2, "Revert rules failed";
}

// Verify correct storage changes for non reverting transfer
rule transfer(address to, uint256 value) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    address other;
    require other != e.msg.sender && other != to;

    mathint balanceOfSenderBefore = balanceOf(e.msg.sender);
    mathint balanceOfToBefore = balanceOf(to);
    mathint balanceOfOtherBefore = balanceOf(other);

    transfer(e, to, value);

    mathint balanceOfSenderAfter = balanceOf(e.msg.sender);
    mathint balanceOfToAfter = balanceOf(to);
    mathint balanceOfOtherAfter = balanceOf(other);

    assert e.msg.sender != to => balanceOfSenderAfter == balanceOfSenderBefore - value, "Assert 1";
    assert e.msg.sender != to => balanceOfToAfter == balanceOfToBefore + value, "Assert 2";
    assert e.msg.sender == to => balanceOfSenderAfter == balanceOfSenderBefore, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
}

// Verify revert rules on transfer
rule transfer_revert(address to, uint256 value) {
    env e;

    mathint balanceOfSender = balanceOf(e.msg.sender);

    transfer@withrevert(e, to, value);

    bool revert1 = e.msg.value > 0;
    bool revert2 = to == 0 || to == currentContract;
    bool revert3 = balanceOfSender < to_mathint(value);

    assert lastReverted <=> revert1 || revert2 || revert3, "Revert rules failed";
}

// Verify correct storage changes for non reverting transferFrom
rule transferFrom(address from, address to, uint256 value) {
    env e;

    requireInvariant balanceSum_equals_totalSupply();

    address other;
    require other != from && other != to;
    address other2; address other3;
    require other2 != from || other3 != e.msg.sender;

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfFromBefore = balanceOf(from);
    mathint balanceOfToBefore = balanceOf(to);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint allowanceFromSenderBefore = allowance(from, e.msg.sender);
    mathint allowanceOtherBefore = allowance(other2, other3);

    transferFrom(e, from, to, value);

    mathint balanceOfFromAfter = balanceOf(from);
    mathint balanceOfToAfter = balanceOf(to);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint allowanceFromSenderAfter = allowance(from, e.msg.sender);
    mathint allowanceOtherAfter = allowance(other2, other3);

    assert from != to => balanceOfFromAfter == balanceOfFromBefore - value, "Assert 1";
    assert from != to => balanceOfToAfter == balanceOfToBefore + value, "Assert 2";
    assert from == to => balanceOfFromAfter == balanceOfFromBefore, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert e.msg.sender != from && allowanceFromSenderBefore != max_uint256 => allowanceFromSenderAfter == allowanceFromSenderBefore - value, "Assert 5";
    assert e.msg.sender == from => allowanceFromSenderAfter == allowanceFromSenderBefore, "Assert 6";
    assert allowanceFromSenderBefore == max_uint256 => allowanceFromSenderAfter == allowanceFromSenderBefore, "Assert 7";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 8";
}

// Verify revert rules on transferFrom
rule transferFrom_revert(address from, address to, uint256 value) {
    env e;

    mathint balanceOfFrom = balanceOf(from);
    mathint allowanceFromSender = allowance(from, e.msg.sender);

    transferFrom@withrevert(e, from, to, value);

    bool revert1 = e.msg.value > 0;
    bool revert2 = to == 0 || to == currentContract;
    bool revert3 = balanceOfFrom < to_mathint(value);
    bool revert4 = allowanceFromSender < to_mathint(value) && e.msg.sender != from;

    assert lastReverted <=> revert1 || revert2 || revert3 || revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting approve
rule approve(address spender, uint256 value) {
    env e;

    address anyUsr; address anyUsr2;
    require anyUsr != e.msg.sender || anyUsr2 != spender;

    mathint allowanceOtherBefore = allowance(anyUsr, anyUsr2);

    approve(e, spender, value);

    mathint allowanceSenderSpenderAfter = allowance(e.msg.sender, spender);
    mathint allowanceOtherAfter = allowance(anyUsr, anyUsr2);

    assert allowanceSenderSpenderAfter == to_mathint(value), "Assert 1";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 2";
}

// Verify revert rules on approve
rule approve_revert(address spender, uint256 value) {
    env e;

    approve@withrevert(e, spender, value);

    bool revert1 = e.msg.value > 0;

    assert lastReverted <=> revert1, "Revert rules failed";
}

// Verify correct behaviour of asset getter
rule asset() {
    env e;

    address asset = asset(e);

    assert asset == usdc(), "Assert 1";
}

// Verify correct behaviour of totalAssets getter
rule totalAssets() {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint totalAssetsCalc = defGetSwapQuote(susds, usdc, totalSupply(), false);

    mathint totalAssets = totalAssets(e);

    assert totalAssets == totalAssetsCalc, "Assert 1";
}

// Verify correct behaviour of convertToShares getter
rule convertToShares(uint256 assets) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint sharesCalc = defGetSwapQuote(usdc, susds, assets, false);

    mathint shares = convertToShares(e, assets);

    assert shares == sharesCalc, "Assert 1";
}

// Verify correct behaviour of convertToAssets getter
rule convertToAssets(uint256 shares) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint assetsCalc = defGetSwapQuote(susds, usdc, shares, false);

    mathint assets = convertToAssets(e, shares);

    assert assets == assetsCalc, "Assert 1";
}

// Verify correct behaviour of maxDeposit getter
rule maxDeposit(address anyAddr) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint maxDepositCalc = defGetSwapQuote(susds, usdc, susds.balanceOf(psm), false);

    mathint maxDeposit = maxDeposit(e, anyAddr);

    assert maxDepositCalc == maxDeposit, "Assert 1";
}

// Verify correct behaviour of previewDeposit getter
rule previewDeposit(uint256 assets) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint previewDepositCalc = defGetSwapQuote(usdc, susds, assets, false);
    mathint previewDeposit = previewDeposit(e, assets);

    assert previewDepositCalc == previewDeposit, "Assert 1";
}

// Verify correct storage changes for non reverting deposit
rule deposit(uint256 assets, address receiver) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint sharesCalc = defGetSwapQuote(usdc, susds, assets, false);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susds.balanceOf(currentContract);
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint shares = deposit(e, assets, receiver);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore - shares, "Assert 7";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 9";
}

// Verify revert rules on deposit
rule deposit_revert(uint256 assets, address receiver) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint susdsBalanceOfPsm = susds.balanceOf(psm);
    mathint shares = defGetSwapQuote(usdc, susds, assets, false);

    // Contracts set up
    require usdc.allowance(currentContract, psm) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require susds.totalSupply() >= susdsBalanceOfPsm + susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require assets * RAY() <= max_uint256;
    require assets * RAY() / rate * psm._susdsPrecision <= max_uint256;
    require assets > 0;

    deposit@withrevert(e, assets, receiver);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > susdsBalanceOfPsm;
    bool revert3 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3, "Revert rules failed";
}

// Verify correct storage changes for non reverting deposit
rule deposit2(uint256 assets, address receiver, uint256 minShares, uint16 referral) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint sharesCalc = defGetSwapQuote(usdc, susds, assets, false);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susds.balanceOf(currentContract);
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint shares = deposit(e, assets, receiver, minShares, referral);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore - shares, "Assert 7";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 9";
}

// Verify revert rules on deposit
rule deposit2_revert(uint256 assets, address receiver, uint256 minShares, uint16 referral) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint susdsBalanceOfPsm = susds.balanceOf(psm);
    mathint shares = defGetSwapQuote(usdc, susds, assets, false);

    // Contracts set up
    require usdc.allowance(currentContract, psm) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require susds.totalSupply() >= susdsBalanceOfPsm + susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require assets * RAY() <= max_uint256;
    require assets * RAY() / rate * psm._susdsPrecision <= max_uint256;
    require assets > 0;

    deposit@withrevert(e, assets, receiver, minShares, referral);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > susdsBalanceOfPsm;
    bool revert3 = shares < minShares;
    bool revert4 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct behaviour of maxMint getter
rule maxMint(address anyAddr) {
    env e;

    mathint maxMintCalc = susds.balanceOf(psm);

    mathint maxMint = maxMint(e, anyAddr);

    assert maxMintCalc == maxMint, "Assert 1";
}

// Verify correct behaviour of previewMint getter
rule previewMint(uint256 shares) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint previewMintCalc = defGetSwapQuote(susds, usdc, shares, true);

    mathint previewMint = previewMint(e, shares);

    assert previewMintCalc == previewMint, "Assert 1";
}

// Verify correct storage changes for non reverting mint
rule mint(uint256 shares, address receiver) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint assetsCalc = defGetSwapQuote(susds, usdc, shares, true);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint assets = mint(e, shares, receiver);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore - shares, "Assert 7";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 8";
}

// Verify revert rules on mint
rule mint_revert(uint256 shares, address receiver) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint susdsBalanceOfPsm = susds.balanceOf(psm);
    mathint assets = defGetSwapQuote(susds, usdc, shares, true);

    // Contracts set up
    require usdc.allowance(currentContract, psm) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require susds.totalSupply() >= susdsBalanceOfPsm + susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require shares * rate <= max_uint256;
    require shares * rate / RAY() * psm._usdcPrecision <= max_uint256;
    require shares > 0;

    mint@withrevert(e, shares, receiver);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > susdsBalanceOfPsm;
    bool revert3 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3, "Revert rules failed";
}

// Verify correct storage changes for non reverting mint
rule mint2(uint256 shares, address receiver, uint256 maxAssets, uint16 referral) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint assetsCalc = defGetSwapQuote(susds, usdc, shares, true);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint assets = mint(e, shares, receiver, maxAssets, referral);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore - shares, "Assert 7";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 8";
}

// Verify revert rules on mint
rule mint2_revert(uint256 shares, address receiver, uint256 maxAssets, uint16 referral) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint susdsBalanceOfPsm = susds.balanceOf(psm);
    mathint assets = defGetSwapQuote(susds, usdc, shares, true);

    // Contracts set up
    require usdc.allowance(currentContract, psm) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require susds.totalSupply() >= susdsBalanceOfPsm + susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require shares * rate <= max_uint256;
    require shares * rate / RAY() * psm._usdcPrecision <= max_uint256;
    require shares > 0;

    mint@withrevert(e, shares, receiver, maxAssets, referral);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > susdsBalanceOfPsm;
    bool revert3 = assets > maxAssets;
    bool revert4 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct behaviour of maxWithdraw getter
rule maxWithdraw(address owner) {
    env e;

    mathint maxWithdrawCalc = _min(
                                (balanceOf(owner) / 10^12) * rateProvider.getConversionRate() / RAY(),
                                usdc.balanceOf(psm.pocket())
                            );

    mathint maxWithdraw = maxWithdraw(e, owner);

    assert maxWithdrawCalc == maxWithdraw, "Assert 1";
}

// Verify correct behaviour of previewWithdraw getter
rule previewWithdraw(uint256 assets) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint previewWithdrawCalc = defGetSwapQuote(usdc, susds, assets, true);

    mathint previewWithdraw = previewWithdraw(e, assets);

    assert previewWithdrawCalc == previewWithdraw, "Assert 1";
}

// Verify correct storage changes for non reverting withdraw
rule withdraw(uint256 assets, address receiver, address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint sharesCalc = defGetSwapQuote(usdc, susds, assets, true);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susds.totalSupply();
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint shares = withdraw(e, assets, receiver, owner);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore + shares, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 9";
}

// Verify revert rules on withdraw
rule withdraw_revert(uint256 assets, address receiver, address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);

    mathint shares = defGetSwapQuote(usdc, susds, assets, true);

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require susds.allowance(currentContract, psm) == max_uint256;

    // Contract behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(pocket) + usdc.balanceOf(currentContract) + usdc.balanceOf(receiver);
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm);

    // Avoid external contracts overflows
    require assets * RAY() <= max_uint256;
    require defCeilDiv(assets * RAY(), rate) * psm._susdsPrecision <= max_uint256;
    require assets > 0;
    require receiver != 0;

    withdraw@withrevert(e, assets, receiver, owner);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > balanceOfOwner;
    bool revert3 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert4 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting withdraw
rule withdraw2(uint256 assets, address receiver, address owner, uint256 maxShares) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint sharesCalc = defGetSwapQuote(usdc, susds, assets, true);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susds.totalSupply();
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint shares = withdraw(e, assets, receiver, owner, maxShares);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore + shares, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 9";
}


// Verify revert rules on withdraw
rule withdraw2_revert(uint256 assets, address receiver, address owner, uint256 maxShares) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);

    mathint shares = defGetSwapQuote(usdc, susds, assets, true);

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require susds.allowance(currentContract, psm) == max_uint256;

    // Contract behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(pocket) + usdc.balanceOf(currentContract) + usdc.balanceOf(receiver);
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm);

    // Avoid external contracts overflows
    require assets * RAY() <= max_uint256;
    require defCeilDiv(assets * RAY(), rate) * psm._susdsPrecision <= max_uint256;
    require assets > 0;
    require receiver != 0;

    withdraw@withrevert(e, assets, receiver, owner, maxShares);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > balanceOfOwner;
    bool revert3 = shares > maxShares;
    bool revert4 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert5 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5, "Revert rules failed";
}

// Verify correct behaviour of maxRedeem getter
rule maxRedeem(address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint maxRedeemCalc = _min(
                                balanceOf(owner),
                                defGetSwapQuote(usdc, susds, usdc.balanceOf(psm.pocket()), false)
                            );

    mathint maxRedeem = maxRedeem(e, owner);

    assert maxRedeemCalc == maxRedeem, "Assert 1";
}

// Verify correct behaviour of previewRedeem getter
rule previewRedeem(uint256 shares) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    mathint previewRedeemCalc = defGetSwapQuote(susds, usdc, shares, false);

    mathint previewRedeem = previewRedeem(e, shares);

    assert previewRedeemCalc == previewRedeem, "Assert 1";
}

// Verify correct storage changes for non reverting redeem
rule redeem(uint256 shares, address receiver, address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint assetsCalc = defGetSwapQuote(susds, usdc, shares, false);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susds.totalSupply();
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint assets = redeem(e, shares, receiver, owner);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore + shares, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 9";
}

// Verify revert rules on redeem
rule redeem_revert(uint256 shares, address receiver, address owner) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);

    mathint assets = defGetSwapQuote(susds, usdc, shares, false);

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require susds.allowance(currentContract, psm) == max_uint256;

    // Contract behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(pocket) + usdc.balanceOf(currentContract) + usdc.balanceOf(receiver);
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm);

    // Avoid external contracts overflows
    require shares * rate <= max_uint256;
    require (shares * rate / RAY()) * psm._usdcPrecision <= max_uint256;
    require shares > 0;
    require receiver != 0;

    redeem@withrevert(e, shares, receiver, owner);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > balanceOfOwner;
    bool revert3 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert4 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting redeem
rule redeem2(uint256 shares, address receiver, address owner, uint256 minAssets) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint assetsCalc = defGetSwapQuote(susds, usdc, shares, false);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmBefore = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susds.totalSupply();
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint assets = redeem(e, shares, receiver, owner, minAssets);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint susdsBalanceOfPsmAfter = susds.balanceOf(psm);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert susdsBalanceOfPsmAfter == susdsBalanceOfPsmBefore + shares, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 9";
}

// Verify revert rules on redeem
rule redeem2_revert(uint256 shares, address receiver, address owner, uint256 minAssets) {
    env e;

    require psm._susdsPrecision == 10^18;
    require psm._usdcPrecision == 10^6;

    address pocket = psm.pocket();

    mathint rate = rateProvider.getConversionRate();
    require rate >= RAY() && rate <= 10 * RAY(); // Logical rate

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);

    mathint assets = defGetSwapQuote(susds, usdc, shares, false);

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require susds.allowance(currentContract, psm) == max_uint256;

    // Contract behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(pocket) + usdc.balanceOf(currentContract) + usdc.balanceOf(receiver);
    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(psm);

    // Avoid external contracts overflows
    require shares * rate <= max_uint256;
    require (shares * rate / RAY()) * psm._usdcPrecision <= max_uint256;
    require shares > 0;
    require receiver != 0;

    redeem@withrevert(e, shares, receiver, owner, minAssets);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > balanceOfOwner;
    bool revert3 = assets < minAssets;
    bool revert4 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert5 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5, "Revert rules failed";
}

// Verify correct storage changes for non reverting exit
rule exit(uint256 shares, address receiver, address owner) {
    env e;

    address other;
    require other != owner;

    mathint usdsOutSUsds = susds.previewRedeem(e, shares);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);
    mathint susdsBalanceOfReceiverBefore = susds.balanceOf(receiver);

    require totalSupplyBefore <= susds.totalSupply();
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    exit(e, shares, receiver, owner);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);
    mathint susdsBalanceOfReceiverAfter = susds.balanceOf(receiver);

    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 1";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 2";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 3";
    assert receiver != currentContract => susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 4";
    assert receiver != currentContract => susdsBalanceOfReceiverAfter == susdsBalanceOfReceiverBefore + shares, "Assert 5";
    assert receiver == currentContract => susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore, "Assert 6";
}

// Verify revert rules on exit
rule exit_revert(uint256 shares, address receiver, address owner) {
    env e;

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);

    require susds.totalSupply() >= susds.balanceOf(currentContract) + susds.balanceOf(receiver);
    require totalSupply() >= balanceOf(owner); // TODO: See if we can make the invariant to work

    // Behavior coming from deposit/mint functions
    require susds.balanceOf(currentContract) >= totalSupply();

    exit@withrevert(e, shares, receiver, owner);

    bool revert1 = e.msg.value > 0;
    bool revert2 = shares > balanceOfOwner;
    bool revert3 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert4 = receiver == 0 || receiver == susds;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting permit
rule permitVRS(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;

    address anyUsr; address anyUsr2;
    require anyUsr != owner || anyUsr2 != spender;
    address other;
    require other != owner;

    mathint allowanceOtherBefore = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerBefore = nonces(owner);
    mathint noncesOtherBefore = nonces(other);

    permit(e, owner, spender, value, deadline, v, r, s);

    mathint allowanceOwnerSpenderAfter = allowance(owner, spender);
    mathint allowanceOtherAfter = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerAfter = nonces(owner);
    mathint noncesOtherAfter = nonces(other);

    assert allowanceOwnerSpenderAfter == to_mathint(value), "Assert 1";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 2";
    assert noncesOwnerBefore < max_uint256 => noncesOwnerAfter == noncesOwnerBefore + 1, "Assert 3";
    assert noncesOwnerBefore == max_uint256 => noncesOwnerAfter == 0, "Assert 4";
    assert noncesOtherAfter == noncesOtherBefore, "Assert 5";
}

// Verify revert rules on permit
rule permitVRS_revert(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) {
    env e;

    bytes32 digest = aux.computeDigestForToken(
                        DOMAIN_SEPARATOR(),
                        PERMIT_TYPEHASH(),
                        owner,
                        spender,
                        value,
                        nonces(owner),
                        deadline
                    );
    address ownerRecover = aux.call_ecrecover(digest, v, r, s);
    bytes32 returnedSig = owner == signer ? signer.isValidSignature(e, digest, aux.VRSToSignature(v, r, s)) : to_bytes32(0);

    permit@withrevert(e, owner, spender, value, deadline, v, r, s);

    bool revert1 = e.msg.value > 0;
    bool revert2 = e.block.timestamp > deadline;
    bool revert3 = owner == 0;
    bool revert4 = owner != ownerRecover && returnedSig != to_bytes32(0x1626ba7e00000000000000000000000000000000000000000000000000000000);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting permit
rule permitSignature(address owner, address spender, uint256 value, uint256 deadline, bytes signature) {
    env e;

    address anyUsr; address anyUsr2;
    require anyUsr != owner || anyUsr2 != spender;
    address other;
    require other != owner;

    mathint allowanceOtherBefore = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerBefore = nonces(owner);
    mathint noncesOtherBefore = nonces(other);

    permit(e, owner, spender, value, deadline, signature);

    mathint allowanceOwnerSpenderAfter = allowance(owner, spender);
    mathint allowanceOtherAfter = allowance(anyUsr, anyUsr2);
    mathint noncesOwnerAfter = nonces(owner);
    mathint noncesOtherAfter = nonces(other);

    assert allowanceOwnerSpenderAfter == to_mathint(value), "Assert 1";
    assert allowanceOtherAfter == allowanceOtherBefore, "Assert 2";
    assert noncesOwnerBefore < max_uint256 => noncesOwnerAfter == noncesOwnerBefore + 1, "Assert 3";
    assert noncesOwnerBefore == max_uint256 => noncesOwnerAfter == 0, "Assert 4";
    assert noncesOtherAfter == noncesOtherBefore, "Assert 5";
}

// Verify revert rules on permit
rule permitSignature_revert(address owner, address spender, uint256 value, uint256 deadline, bytes signature) {
    env e;

    bytes32 digest = aux.computeDigestForToken(
                        DOMAIN_SEPARATOR(),
                        PERMIT_TYPEHASH(),
                        owner,
                        spender,
                        value,
                        nonces(owner),
                        deadline
                    );
    uint8 v; bytes32 r; bytes32 s;
    v, r, s = aux.signatureToVRS(signature);
    address null_address = 0;
    address ownerRecover = aux.size(signature) == 65 ? aux.call_ecrecover(digest, v, r, s) : null_address;
    bytes32 returnedSig = owner == signer ? signer.isValidSignature(e, digest, signature) : to_bytes32(0);

    permit@withrevert(e, owner, spender, value, deadline, signature);

    bool revert1 = e.msg.value > 0;
    bool revert2 = e.block.timestamp > deadline;
    bool revert3 = owner == 0;
    bool revert4 = owner != ownerRecover && returnedSig != to_bytes32(0x1626ba7e00000000000000000000000000000000000000000000000000000000);

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}
