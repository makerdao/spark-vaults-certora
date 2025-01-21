// UsdcVault.spec

using SUsdsMock as susds;
using PsmMock as psm;
using PsmWrapperMock as psmWrap;
using UsdcMock as usdc;
using DaiMock as dai;
using UsdsMock as usds;
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
    function psm() external returns (address) envfree;
    function susds() external returns (address) envfree;
    function usdc() external returns (address) envfree;
    //
    function DOMAIN_SEPARATOR() external returns (bytes32) envfree;
    function PERMIT_TYPEHASH() external returns (bytes32) envfree;
    //
    function psm.tin() external returns (uint256) envfree;
    function psm.tout() external returns (uint256) envfree;
    function psm.pocket() external returns (address) envfree;
    function susds.chi() external returns (uint192) envfree;
    function susds.rho() external returns (uint64) envfree;
    function susds.ssr() external returns (uint256) envfree;
    function susds.balanceOf(address) external returns (uint256) envfree;
    function susds.totalSupply() external returns (uint256) envfree;
    function usdc.allowance(address, address) external returns (uint256) envfree;
    function usdc.balanceOf(address) external returns (uint256) envfree;
    function usdc.totalSupply() external returns (uint256) envfree;
    function dai.allowance(address, address) external returns (uint256) envfree;
    function dai.balanceOf(address) external returns (uint256) envfree;
    function dai.totalSupply() external returns (uint256) envfree;
    function usds.allowance(address, address) external returns (uint256) envfree;
    function usds.balanceOf(address) external returns (uint256) envfree;
    function usds.totalSupply() external returns (uint256) envfree;
    function aux.call_ecrecover(bytes32, uint8, bytes32, bytes32) external returns (address) envfree;
    function aux.computeDigestForToken(bytes32, bytes32, address, address, uint256, uint256, uint256) external returns (bytes32) envfree;
    function aux.signatureToVRS(bytes) external returns (uint8, bytes32, bytes32) envfree;
    function aux.VRSToSignature(uint8, bytes32, bytes32) external returns (bytes) envfree;
    function aux.size(bytes) external returns (uint256) envfree;
    //
    function _.transfer(address,uint256) external => DISPATCHER(true);
    function _.gem() external => DISPATCHER(true);
    function _.pocket() external => DISPATCHER(true);
    function _.psm() external => DISPATCHER(true);
    function _.dai() external => DISPATCHER(true);
    function _.isValidSignature(bytes32, bytes) external => DISPATCHER(true);
}

definition WAD() returns mathint = 10^18;
definition RAY() returns mathint = 10^27;
definition _divup(mathint x, mathint y) returns mathint = x != 0 ? ((x - 1) / y) + 1 : 0;
definition _min(mathint x, mathint y) returns mathint = x < y ? x : y;

definition defPsmUsdsInToGemOut(mathint usdsAmount, mathint tout_) returns mathint = usdsAmount * 10^6 / (WAD() + tout_);
definition defPsmGemOutToUsdsIn(mathint gemAmount, mathint tout_) returns mathint = gemAmount * 10^12 + gemAmount * 10^12 * tout_ / WAD();
definition defPsmUsdsOutToGemInRoundingUp(mathint usdsAmount, mathint tin_) returns mathint = _divup(usdsAmount * 10^6, WAD() - tin_);
definition defPsmUsdsOutToGemInRoundingDown(mathint usdsAmount, mathint tin_) returns mathint = usdsAmount * 10^6 / (WAD() - tin_);
definition defPsmGemInToUsdsOut(mathint gemAmount, mathint tin_) returns mathint = gemAmount * 10^12 - gemAmount * 10^12 * tin_ / WAD();

definition defSusdsConvertToShares(mathint assets) returns mathint = assets * RAY() / susds.chi();
definition defSusdsConvertToAssets(mathint shares) returns mathint = shares * susds.chi() / RAY();
definition defSusdsPreviewDeposit(mathint assets) returns mathint = assets * RAY() / susds.chi();
definition defSusdsPreviewMint(mathint shares) returns mathint = _divup(shares * susds.chi(), RAY());
definition defSusdsPreviewWithdraw(mathint assets) returns mathint = _divup(assets * RAY(), susds.chi());
definition defSusdsPreviewRedeem(mathint shares) returns mathint = shares * susds.chi() / RAY();

ghost usds_balanceSum() returns mathint {
    init_state axiom usds_balanceSum() == 0;
}
hook Sstore usds.balanceOf[KEY address a] uint256 balance (uint256 old_balance) {
    havoc usds_balanceSum assuming usds_balanceSum@new() == usds_balanceSum@old() + balance - old_balance;
}
invariant usds_balanceSum_equals_totalSupply() usds_balanceSum() == to_mathint(usds.totalSupply())
            filtered {
                m -> m.selector != sig:upgradeToAndCall(address, bytes).selector
            }

ghost susds_balanceSum() returns mathint {
    init_state axiom susds_balanceSum() == 0;
}
hook Sstore susds.balanceOf[KEY address a] uint256 balance (uint256 old_balance) {
    havoc susds_balanceSum assuming susds_balanceSum@new() == susds_balanceSum@old() + balance - old_balance;
}
invariant susds_balanceSum_equals_totalSupply() susds_balanceSum() == to_mathint(susds.totalSupply()) 
            filtered {
                m -> m.selector != sig:upgradeToAndCall(address, bytes).selector
            } {
            preserved {
                requireInvariant usds_balanceSum_equals_totalSupply;
            }
}
ghost balanceSum() returns mathint {
    init_state axiom balanceSum() == 0;
}
hook Sstore balanceOf[KEY address a] uint256 balance (uint256 old_balance) {
    havoc balanceSum assuming balanceSum@new() == balanceSum@old() + balance - old_balance && balanceSum@new() >= 0;
}
invariant balanceSum_equals_totalSupply() balanceSum() <= susds_balanceSum() && balanceSum() == to_mathint(totalSupply())
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

rule invariant_vault_usdc_balance_is_0(method f) filtered { f -> !f.isView } {
    env e;

    address pocket = psm.pocket();
    require pocket == currentContract.pocket;
    require pocket != currentContract;
    
    require usdc.balanceOf(currentContract) == 0;

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
}

rule invariant_vault_usds_dust_only_increasing_and_capped(method f) filtered { f -> !f.isView } {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi
    require psm.tout() <= WAD(); // Logical tout

    mathint usdsBalanceOfVaultBefore = usds.balanceOf(currentContract);

    calldataarg args;
    f(e, args);

    mathint usdsBalanceOfVaultAfter = usds.balanceOf(currentContract);

    assert usdsBalanceOfVaultAfter >= usdsBalanceOfVaultBefore && usdsBalanceOfVaultAfter <= usdsBalanceOfVaultBefore + 1000 * 10^12, "Assert 1";
}

rule invariant_maxDeposit(address anyAddr) {
    env e;

    require psm.tin() < WAD();
    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi
    
    address receiver;
    require receiver != 0 && receiver != currentContract;

    uint256 maxDeposit = maxDeposit(e, anyAddr);
    require maxDeposit > 0;

    // Contracts set up
    require usdc.allowance(currentContract, psmWrap) == max_uint256;
    require usdc.allowance(psmWrap, psm) == max_uint256;
    require usds.allowance(currentContract, susds) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= maxDeposit;
    require usdc.balanceOf(e.msg.sender) >= maxDeposit;

    // Avoid overflows
    require maxDeposit * 10^12 * psm.tin() <= max_uint256;
    require maxDeposit * 10^12 - maxDeposit * 10^12 * psm.tin() / 10 ^ 18 + usds.totalSupply() <= max_uint256;
    require (maxDeposit * 10^12 - maxDeposit * 10^12 * psm.tin() / WAD()) * RAY() <= max_uint256;
    require susds.totalSupply() + (maxDeposit * 10^12 - maxDeposit * 10^12 * psm.tin() / WAD()) * RAY() / susds.chi() <= max_uint256;

    mathint daiBalanceOfPSMBefore = dai.balanceOf(psm);

    deposit@withrevert(e, maxDeposit, receiver);
    bool lastRevertedValue = lastReverted;

    mathint daiBalanceOfPSMAfter = dai.balanceOf(psm);
    mathint maxDepositAfter = maxDeposit(e, anyAddr);

    assert !lastRevertedValue, "Assert 1";
    assert daiBalanceOfPSMAfter <= 10^12, "Assert 2";
    assert maxDepositAfter == 0, "Assert 3";
}

rule invariant_maxMint(address anyAddr) {
    env e;

    require psm.tin() < WAD();
    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi
    
    address receiver;
    require receiver != 0 && receiver != currentContract;

    uint256 maxMint = maxMint(e, anyAddr);
    require maxMint > 0;

    // Contracts set up
    require usdc.allowance(currentContract, psmWrap) == max_uint256;
    require usdc.allowance(psmWrap, psm) == max_uint256;
    require usds.allowance(currentContract, susds) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);

    mathint assets = previewMint(e, maxMint);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid overflows
    require assets * 10^12 * psm.tin() <= max_uint256;
    require assets * 10^12 - assets * 10^12 * psm.tin() / 10 ^ 18 + usds.totalSupply() <= max_uint256; 
    require susds.totalSupply() + maxMint <= max_uint256;

    mathint daiBalanceOfPSMBefore = dai.balanceOf(psm);

    mint@withrevert(e, maxMint, receiver);
    bool lastRevertedValue = lastReverted;

    mathint daiBalanceOfPSMAfter = dai.balanceOf(psm);
    mathint maxMintAfter = maxMint(e, anyAddr);

    assert !lastRevertedValue, "Assert 1";
    assert daiBalanceOfPSMAfter <= 10^12, "Assert 2";
    assert maxMintAfter == 0, "Assert 3";
}

rule invariant_maxWithdraw(address owner) {
    env e;

    require psm.tout() < WAD();
    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;

    address receiver;
    require receiver != 0 && receiver != currentContract && receiver != pocket;

    uint256 maxWithdraw = maxWithdraw(e, owner);
    require maxWithdraw > 0;

    mathint shares = defSusdsPreviewWithdraw(maxWithdraw);

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require usds.allowance(currentContract, psmWrap) == max_uint256;
    require dai.allowance(psmWrap, psm) == max_uint256;

    // Vault behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // Susds behavior
    require usds.balanceOf(susds) >= _divup(susds.totalSupply() * susds.chi(), RAY());

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket()) + usdc.balanceOf(receiver);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(susds) + usds.balanceOf(psm);
    require susds.totalSupply() >= susds.balanceOf(currentContract);
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);

    // Owner => sender allowance
    require allowance(owner, e.msg.sender) == max_uint256;

    // Avoid overflows
    require maxWithdraw * 10^12 * psm.tout() <= max_uint256;
    require (maxWithdraw * 10^12 + maxWithdraw * 10^12 * psm.tout() / WAD()) * RAY() <= max_uint256;
    require dai.totalSupply() + (maxWithdraw * 10^12 + maxWithdraw * 10^12 * psm.tout() / WAD()) <= max_uint256;

    withdraw@withrevert(e, maxWithdraw, receiver, owner);
    bool lastRevertedValue = lastReverted;

    mathint maxWithdrawAfter = maxWithdraw(e, owner);

    assert !lastRevertedValue, "Assert 1";
    assert maxWithdrawAfter <= 10^12, "Assert 2";
}

rule invariant_maxRedeem(address owner) {
    env e;

    require psm.tout() < WAD();
    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;

    address receiver;
    require receiver != 0 && receiver != currentContract && receiver != pocket;

    uint256 maxRedeem = maxRedeem(e, owner);
    require maxRedeem > 0;

    mathint assets = defPsmUsdsInToGemOut(defSusdsPreviewRedeem(maxRedeem), psm.tout());

    // Contracts set up
    require usdc.allowance(pocket, psm) == max_uint256;
    require usds.allowance(currentContract, psmWrap) == max_uint256;
    require dai.allowance(psmWrap, psm) == max_uint256;

    // Vault behavior
    require susds.balanceOf(currentContract) >= totalSupply();
    require totalSupply() >= balanceOf(owner);

    // Susds behavior
    require usds.balanceOf(susds) >= _divup(susds.totalSupply() * susds.chi(), RAY());

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket()) + usdc.balanceOf(receiver);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(susds) + usds.balanceOf(psm);
    require susds.totalSupply() >= susds.balanceOf(currentContract);
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);

    // Owner => sender allowance
    require allowance(owner, e.msg.sender) == max_uint256;

    // Avoid overflows
    require maxRedeem * susds.chi() <= max_uint256;
    require maxRedeem * susds.chi() / RAY() * 10^6 <= max_uint256;
    require dai.totalSupply() + assets * 10^12 + assets * 10^12 * psm.tout() / WAD() <= max_uint256;

    redeem@withrevert(e, maxRedeem, receiver, owner);
    bool lastRevertedValue = lastReverted;

    mathint maxRedeemAfter = maxRedeem(e, owner);

    assert !lastRevertedValue, "Assert 1";
    assert maxRedeemAfter <= 2 * 10^12 - 1, "Assert 2";
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

// Verify correct behaviour of chi getter
rule chi() {
    env e;

    mathint chi = chi(e);

    assert chi == susds.chi(), "Assert 1";
}

// Verify correct behaviour of rho getter
rule rho() {
    env e;

    mathint rho = rho(e);

    assert rho == susds.rho(), "Assert 1";
}

// Verify correct behaviour of ssr getter
rule ssr() {
    env e;

    mathint ssr = ssr(e);

    assert ssr == susds.ssr(), "Assert 1";
}

// Verify correct behaviour of tin getter
rule tin() {
    env e;

    mathint tin = tin(e);

    assert tin == psm.tin(), "Assert 1";
}

// Verify correct behaviour of tout getter
rule tout() {
    env e;

    mathint tout = tout(e);

    assert tout == psm.tout(), "Assert 1";
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

    mathint totalAssetsCalc = defSusdsConvertToAssets(totalSupply()) / 10^12;

    mathint totalAssets = totalAssets(e);

    assert totalAssets == totalAssetsCalc, "Assert 1";
}

// Verify correct behaviour of convertToShares getter
rule convertToShares(uint256 assets) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint sharesCalc = defSusdsConvertToShares(assets * 10^12);

    mathint shares = convertToShares(e, assets);

    assert shares == sharesCalc, "Assert 1";
}

// Verify correct behaviour of convertToAssets getter
rule convertToAssets(uint256 shares) {
    env e;

    mathint assetsCalc = defSusdsConvertToAssets(shares) / 10^12;

    mathint assets = convertToAssets(e, shares);

    assert assets == assetsCalc, "Assert 1";
}

// Verify correct behaviour of maxDeposit getter
rule maxDeposit(address anyAddr) {
    env e;

    mathint tin_ = psm.tin();
    mathint maxDepositCalc = tin_ >= WAD() ? 0 : defPsmUsdsOutToGemInRoundingDown(dai.balanceOf(psm), tin_);

    mathint maxDeposit = maxDeposit(e, anyAddr);

    assert maxDepositCalc == maxDeposit, "Assert 1";
}

// Verify correct behaviour of previewDeposit getter
rule previewDeposit(uint256 assets) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint previewDepositCalc = defSusdsPreviewDeposit(defPsmGemInToUsdsOut(assets, psm.tin()));

    mathint previewDeposit = previewDeposit(e, assets);

    assert previewDepositCalc == previewDeposit, "Assert 1";
}

// Verify correct storage changes for non reverting deposit
rule deposit(uint256 assets, address receiver) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint tin_ = psm.tin();

    mathint daiOutPsm = defPsmGemInToUsdsOut(assets, tin_);
    mathint sharesCalc = defSusdsPreviewDeposit(daiOutPsm);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint shares = deposit(e, assets, receiver);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore - daiOutPsm, "Assert 7";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore + daiOutPsm, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 9";
}

// Verify revert rules on deposit
rule deposit_revert(uint256 assets, address receiver) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint tin_ = psm.tin();
    mathint daiBalanceOfPsm = dai.balanceOf(psm);
    mathint daiOutPsm = defPsmGemInToUsdsOut(assets, tin_);

    // Contracts set up
    require usdc.allowance(currentContract, psmWrap) == max_uint256;
    require usdc.allowance(psmWrap, psm) == max_uint256;
    require usds.allowance(currentContract, susds) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require assets * 10^12 * psm.tin() <= max_uint256;
    require usds.totalSupply() + assets * 10^12 - assets * 10^12 * psm.tin() / 10 ^ 18 <= max_uint256;
    require daiOutPsm * RAY() <= max_uint256;
    require susds.totalSupply() + daiOutPsm * RAY() / susds.chi() <= max_uint256;

    deposit@withrevert(e, assets, receiver);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tin_ >= WAD();
    bool revert3 = daiOutPsm > daiBalanceOfPsm;
    bool revert4 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting deposit
rule deposit2(uint256 assets, address receiver, uint256 minShares, uint16 referral) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint tin_ = psm.tin();

    mathint daiOutPsm = defPsmGemInToUsdsOut(assets, tin_);
    mathint sharesCalc = defSusdsPreviewDeposit(daiOutPsm);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint shares = deposit(e, assets, receiver, minShares, referral);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore - daiOutPsm, "Assert 7";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore + daiOutPsm, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 9";
}

// Verify revert rules on deposit
rule deposit2_revert(uint256 assets, address receiver, uint256 minShares, uint16 referral) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint tin_ = psm.tin();
    mathint daiBalanceOfPsm = dai.balanceOf(psm);
    mathint daiOutPsm = defPsmGemInToUsdsOut(assets, tin_);
    mathint shares = daiOutPsm * RAY() / susds.chi();

    // Contracts set up
    require usdc.allowance(currentContract, psmWrap) == max_uint256;
    require usdc.allowance(psmWrap, psm) == max_uint256;
    require usds.allowance(currentContract, susds) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require assets * 10^12 * psm.tin() <= max_uint256;
    require assets * 10^12 - assets * 10^12 * psm.tin() / 10 ^ 18 + usds.totalSupply() <= max_uint256;
    require daiOutPsm * RAY() <= max_uint256;
    require susds.totalSupply() + daiOutPsm * RAY() / susds.chi() <= max_uint256;

    deposit@withrevert(e, assets, receiver, minShares, referral);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tin_ >= WAD();
    bool revert3 = daiOutPsm > daiBalanceOfPsm;
    bool revert4 = shares < minShares;
    bool revert5 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5, "Revert rules failed";
}

// Verify correct behaviour of maxMint getter
rule maxMint(address anyAddr) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint tin_ = psm.tin();
    mathint maxMintCalc;
    if(tin_ >= WAD()) {
        maxMintCalc = 0;
    } else {
        maxMintCalc = defSusdsPreviewDeposit(defPsmUsdsOutToGemInRoundingDown(dai.balanceOf(psm), tin_) * (WAD() - tin_) / 10^6);
    } 

    mathint maxMint = maxMint(e, anyAddr);

    assert maxMintCalc == maxMint, "Assert 1";
}

// Verify correct behaviour of previewMint getter
rule previewMint(uint256 shares) {
    env e;

    mathint tin_ =  psm.tin();
    mathint previewMintCalc;
    if (tin_ < WAD()) {
        previewMintCalc = defPsmUsdsOutToGemInRoundingUp(defSusdsPreviewMint(shares), psm.tin());
    } else {
        previewMintCalc = 0; // This path should revert, so any random value is fine
    }

    mathint previewMint = previewMint(e, shares);

    assert previewMintCalc == previewMint, "Assert 1";
}

// Verify correct storage changes for non reverting mint
rule mint(uint256 shares, address receiver) {
    env e;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint tin_ = psm.tin();
    mathint stakedUsds = defSusdsPreviewMint(shares);
    mathint assetsCalc;
    if (tin_ < WAD()) {
        assetsCalc = defPsmUsdsOutToGemInRoundingUp(stakedUsds, psm.tin());
    } else {
        assetsCalc = 0; // This path should revert, so any random value is fine
    }
    mathint daiOutPsm = defPsmGemInToUsdsOut(assetsCalc, tin_);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint assets = mint(e, shares, receiver);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore - daiOutPsm, "Assert 7";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore + stakedUsds, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 9";
    assert stakedUsds <= daiOutPsm, "Assert 10";
    assert stakedUsds >= daiOutPsm - 10^12, "Assert 11";
}

// Verify revert rules on mint
rule mint_revert(uint256 shares, address receiver) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint tin_ = psm.tin();
    mathint daiBalanceOfPsm = dai.balanceOf(psm);
    mathint stakedUsds = defSusdsPreviewMint(shares);
    mathint assets;
    if (tin_ < WAD()) {
        assets = defPsmUsdsOutToGemInRoundingUp(stakedUsds, psm.tin());
    } else {
        assets = 0; // This path should revert, and will be caught
    }
    mathint daiOutPsm = defPsmGemInToUsdsOut(assets, tin_);

    // Contracts set up
    require usdc.allowance(currentContract, psmWrap) == max_uint256;
    require usdc.allowance(psmWrap, psm) == max_uint256;
    require usds.allowance(currentContract, susds) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require assets * 10^12 * psm.tin() <= max_uint256;
    require assets * 10^12 - assets * 10^12 * psm.tin() / 10 ^ 18 + usds.totalSupply() <= max_uint256;
    require daiOutPsm * RAY() <= max_uint256;
    require susds.totalSupply() + daiOutPsm * RAY() / susds.chi() <= max_uint256;

    mint@withrevert(e, shares, receiver);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tin_ >= WAD();
    bool revert3 = daiOutPsm > daiBalanceOfPsm;
    bool revert4 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4, "Revert rules failed";
}

// Verify correct storage changes for non reverting mint
rule mint2(uint256 shares, address receiver, uint256 maxAssets, uint16 referral) {
    env e;

    address pocket = psm.pocket();
    require e.msg.sender != pocket;

    address other;
    require other != receiver;

    mathint tin_ = psm.tin();
    mathint stakedUsds = defSusdsPreviewMint(shares);
    mathint assetsCalc;
    if (tin_ < WAD()) {
        assetsCalc = defPsmUsdsOutToGemInRoundingUp(stakedUsds, psm.tin());
    } else {
        assetsCalc = 0; // This path should revert, so any random value is fine
    }
    mathint daiOutPsm = defPsmGemInToUsdsOut(assetsCalc, tin_);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfReceiverBefore = balanceOf(receiver);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfSenderBefore = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfReceiverBefore + balanceOfOtherBefore;

    mathint assets = mint(e, shares, receiver, maxAssets, referral);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfReceiverAfter = balanceOf(receiver);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfSenderAfter = usdc.balanceOf(e.msg.sender);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore + shares, "Assert 2";
    assert balanceOfReceiverAfter == balanceOfReceiverBefore + shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert usdcBalanceOfSenderAfter == usdcBalanceOfSenderBefore - assets, "Assert 5";
    assert usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore + assets, "Assert 6";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore - daiOutPsm, "Assert 7";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore + stakedUsds, "Assert 8";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore + shares, "Assert 9";
    assert stakedUsds <= daiOutPsm, "Assert 10";
    assert stakedUsds >= daiOutPsm - 10^12, "Assert 11";
}

// Verify revert rules on mint
rule mint2_revert(uint256 shares, address receiver, uint256 maxAssets, uint16 referral) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint tin_ = psm.tin();
    mathint daiBalanceOfPsm = dai.balanceOf(psm);
    mathint stakedUsds = defSusdsPreviewMint(shares);
    mathint assets;
    if (tin_ < WAD()) {
        assets = defPsmUsdsOutToGemInRoundingUp(stakedUsds, psm.tin());
    } else {
        assets = 0; // This path should revert, and will be caught
    }
    mathint daiOutPsm = defPsmGemInToUsdsOut(assets, tin_);

    // Contracts set up
    require usdc.allowance(currentContract, psmWrap) == max_uint256;
    require usdc.allowance(psmWrap, psm) == max_uint256;
    require usds.allowance(currentContract, susds) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(e.msg.sender) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);

    // Sender assumptions
    require usdc.allowance(e.msg.sender, currentContract) >= assets;
    require usdc.balanceOf(e.msg.sender) >= assets;

    // Avoid external contracts overflows
    require assets * 10^12 * psm.tin() <= max_uint256;
    require assets * 10^12 - assets * 10^12 * psm.tin() / 10 ^ 18 + usds.totalSupply() <= max_uint256;
    require daiOutPsm * RAY() <= max_uint256;
    require susds.totalSupply() + daiOutPsm * RAY() / susds.chi() <= max_uint256;

    mint@withrevert(e, shares, receiver, maxAssets, referral);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tin_ >= WAD();
    bool revert3 = assets > maxAssets;
    bool revert4 = daiOutPsm > daiBalanceOfPsm;
    bool revert5 = receiver == 0 || receiver == currentContract;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5, "Revert rules failed";
}

// Verify correct behaviour of maxWithdraw getter
rule maxWithdraw(address owner) {
    env e;

    // Constructor
    address pocket = psm.pocket();
    require currentContract.pocket == pocket;

    mathint tout_ = psm.tout();
    mathint maxWithdrawCalc = tout_ == max_uint256
                              ? 0
                              : _min(
                                    defPsmUsdsInToGemOut(defSusdsPreviewRedeem(balanceOf(owner)), tout_),
                                    usdc.balanceOf(pocket)
                                );

    mathint maxWithdraw = maxWithdraw(e, owner);

    assert maxWithdrawCalc == maxWithdraw, "Assert 1";
}

// Verify correct behaviour of previewWithdraw getter
rule previewWithdraw(uint256 assets) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint previewWithdrawCalc = defSusdsPreviewWithdraw(defPsmGemOutToUsdsIn(assets, psm.tout()));

    mathint previewWithdraw = previewWithdraw(e, assets);

    assert previewWithdrawCalc == previewWithdraw, "Assert 1";
}

// Verify correct storage changes for non reverting withdraw
rule withdraw(uint256 assets, address receiver, address owner) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint tout_ = psm.tout();
    mathint daiInPsm = defPsmGemOutToUsdsIn(assets, tout_);
    mathint sharesCalc = defSusdsPreviewWithdraw(daiInPsm);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint shares = withdraw(e, assets, receiver, owner);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore + daiInPsm, "Assert 8";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore - daiInPsm, "Assert 9";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 10";
}

// Verify revert rules on withdraw
rule withdraw_revert(uint256 assets, address receiver, address owner) {
    env e;

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);
    mathint tout_ = psm.tout();

    mathint daiInPsm = defPsmGemOutToUsdsIn(assets, tout_);
    mathint shares = defSusdsPreviewWithdraw(daiInPsm);

    // Contracts set up
    require usds.allowance(currentContract, psmWrap) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(receiver) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);
    require totalSupply() >= balanceOf(owner);

    // Behavior coming from deposit/mint functions
    require susds.balanceOf(currentContract) >= totalSupply();

    // Correct behaviour susds
    require usds.balanceOf(susds) >= susds.totalSupply() * susds.chi() / RAY();

    // Setup assumptions
    require usdc.allowance(pocket, psm) == max_uint256;
    require dai.allowance(psmWrap, psm) == max_uint256;

    // Avoid external contracts overflows
    require daiInPsm >= max_uint256 || daiInPsm * RAY() <= max_uint256; // Let it revert in case it does in vault contract
    require dai.totalSupply() + daiInPsm <= max_uint256;

    withdraw@withrevert(e, assets, receiver, owner);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tout_ == max_uint256;
    bool revert3 = assets * 10^12 >= max_uint256;
    bool revert4 = daiInPsm >= max_uint256;
    bool revert5 = shares > balanceOfOwner;
    bool revert6 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert7 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7, "Revert rules failed";
}

// Verify correct storage changes for non reverting withdraw
rule withdraw2(uint256 assets, address receiver, address owner, uint256 maxShares) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint tout_ = psm.tout();
    mathint daiInPsm = defPsmGemOutToUsdsIn(assets, tout_);
    mathint sharesCalc = defSusdsPreviewWithdraw(daiInPsm);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint shares = withdraw(e, assets, receiver, owner, maxShares);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert shares == sharesCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore + daiInPsm, "Assert 8";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore - daiInPsm, "Assert 9";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 10";
}

// Verify revert rules on withdraw
rule withdraw2_revert(uint256 assets, address receiver, address owner, uint256 maxShares) {
    env e;

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);
    mathint tout_ = psm.tout();

    mathint daiInPsm = defPsmGemOutToUsdsIn(assets, tout_);
    mathint shares = defSusdsPreviewWithdraw(daiInPsm);

    // Contracts set up
    require usds.allowance(currentContract, psmWrap) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(receiver) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);
    require totalSupply() >= balanceOf(owner);

    // Behavior coming from deposit/mint functions
    require susds.balanceOf(currentContract) >= totalSupply();

    // Correct behaviour susds
    require usds.balanceOf(susds) >= susds.totalSupply() * susds.chi() / RAY();

    // Setup assumptions
    require usdc.allowance(pocket, psm) == max_uint256;
    require dai.allowance(psmWrap, psm) == max_uint256;

    // Avoid external contracts overflows
    require daiInPsm >= max_uint256 || daiInPsm * RAY() <= max_uint256; // Let it revert in case it does in vault contract
    require dai.totalSupply() + daiInPsm <= max_uint256;

    withdraw@withrevert(e, assets, receiver, owner, maxShares);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tout_ == max_uint256;
    bool revert3 = assets * 10^12 >= max_uint256;
    bool revert4 = daiInPsm >= max_uint256;
    bool revert5 = shares > balanceOfOwner;
    bool revert6 = shares > maxShares;
    bool revert7 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert8 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6 ||
                            revert7 || revert8, "Revert rules failed";
}

// Verify correct behaviour of maxRedeem getter
rule maxRedeem(address owner) {
    env e;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    // Constructor
    address pocket = psm.pocket();
    require currentContract.pocket == pocket;

    mathint tout_ = psm.tout();
    mathint maxRedeemCalc = tout_ == max_uint256
                              ? 0
                              : _min(
                                    balanceOf(owner),
                                    defSusdsPreviewWithdraw(defPsmGemOutToUsdsIn(usdc.balanceOf(pocket), tout_))
                                );

    mathint maxRedeem = maxRedeem(e, owner);

    assert maxRedeemCalc == maxRedeem, "Assert 1";
}

// Verify correct behaviour of previewRedeem getter
rule previewRedeem(uint256 shares) {
    env e;

    mathint previewRedeemCalc = defPsmUsdsInToGemOut(defSusdsPreviewRedeem(shares), psm.tout());

    mathint previewRedeem = previewRedeem(e, shares);

    assert previewRedeemCalc == previewRedeem, "Assert 1";
}

// Verify correct storage changes for non reverting redeem
rule redeem(uint256 shares, address receiver, address owner) {
    env e;

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint tout_ = psm.tout();

    mathint usdsOutSUsds = defSusdsPreviewRedeem(shares);
    mathint assetsCalc = defPsmUsdsInToGemOut(usdsOutSUsds, tout_);
    mathint daiInPsm = defPsmGemOutToUsdsIn(assetsCalc, tout_);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint assets = redeem(e, shares, receiver, owner);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore + daiInPsm, "Assert 8";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore - usdsOutSUsds, "Assert 9";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 10";
}

// Verify revert rules on redeem
rule redeem_revert(uint256 shares, address receiver, address owner) {
    env e;

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);
    mathint tout_ = psm.tout();

    mathint usdsOutSUsds = defSusdsPreviewRedeem(shares);
    mathint assets = defPsmUsdsInToGemOut(usdsOutSUsds, tout_);
    mathint daiInPsm = defPsmGemOutToUsdsIn(assets, tout_);

    // Contracts set up
    require usds.allowance(currentContract, psmWrap) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(receiver) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);
    require totalSupply() >= balanceOf(owner);

    // Behavior coming from deposit/mint functions
    require susds.balanceOf(currentContract) >= totalSupply();

    // Correct behaviour susds
    require usds.balanceOf(susds) >= susds.totalSupply() * susds.chi() / RAY();

    // Setup assumptions
    require usdc.allowance(pocket, psm) == max_uint256;
    require dai.allowance(psmWrap, psm) == max_uint256;

    // Avoid external contracts overflows
    require shares * susds.chi() <= max_uint256;
    require WAD() + tout_ <= max_uint256;
    require dai.totalSupply() + daiInPsm <= max_uint256;

    redeem@withrevert(e, shares, receiver, owner);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tout_ == max_uint256;
    bool revert3 = shares > balanceOfOwner;
    bool revert4 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert5 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5, "Revert rules failed";
}

// Verify correct storage changes for non reverting redeem
rule redeem2(uint256 shares, address receiver, address owner, uint256 minAssets) {
    env e;

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    address other;
    require other != owner;

    mathint tout_ = psm.tout();

    mathint usdsOutSUsds = defSusdsPreviewRedeem(shares);
    mathint assetsCalc = defPsmUsdsInToGemOut(usdsOutSUsds, tout_);
    mathint daiInPsm = defPsmGemOutToUsdsIn(assetsCalc, tout_);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint usdcBalanceOfReceiverBefore = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketBefore = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmBefore = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsBefore = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
    require totalSupplyBefore >= balanceOfOwnerBefore + balanceOfOtherBefore;

    mathint assets = redeem(e, shares, receiver, owner, minAssets);

    mathint totalSupplyAfter = totalSupply();
    mathint balanceOfOwnerAfter = balanceOf(owner);
    mathint balanceOfOtherAfter = balanceOf(other);
    mathint usdcBalanceOfReceiverAfter = usdc.balanceOf(receiver);
    mathint usdcBalanceOfPocketAfter = usdc.balanceOf(pocket);
    mathint daiBalanceOfPsmAfter = dai.balanceOf(psm);
    mathint usdsBalanceOfSUsdsAfter = usds.balanceOf(susds);
    mathint susdsBalanceOfVaultAfter = susds.balanceOf(currentContract);

    assert assets == assetsCalc, "Assert 1";
    assert totalSupplyAfter == totalSupplyBefore - shares, "Assert 2";
    assert balanceOfOwnerAfter == balanceOfOwnerBefore - shares, "Assert 3";
    assert balanceOfOtherAfter == balanceOfOtherBefore, "Assert 4";
    assert receiver != pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore + assets, "Assert 5";
    assert receiver != pocket => usdcBalanceOfPocketAfter == usdcBalanceOfPocketBefore - assets, "Assert 6";
    assert receiver == pocket => usdcBalanceOfReceiverAfter == usdcBalanceOfReceiverBefore, "Assert 7";
    assert daiBalanceOfPsmAfter == daiBalanceOfPsmBefore + daiInPsm, "Assert 8";
    assert usdsBalanceOfSUsdsAfter == usdsBalanceOfSUsdsBefore - usdsOutSUsds, "Assert 9";
    assert susdsBalanceOfVaultAfter == susdsBalanceOfVaultBefore - shares, "Assert 10";
}

// Verify revert rules on redeem
rule redeem2_revert(uint256 shares, address receiver, address owner, uint256 minAssets) {
    env e;

    address pocket = psm.pocket();
    require currentContract.pocket == pocket;
    require e.msg.sender != pocket;

    require susds.chi() >= RAY() && susds.chi() <= 10 * RAY(); // Logical chi

    mathint balanceOfOwner = balanceOf(owner);
    mathint allowanceOwnerSender = allowance(owner, e.msg.sender);
    mathint usdcBalanceOfPocket = usdc.balanceOf(pocket);
    mathint tout_ = psm.tout();

    mathint usdsOutSUsds = defSusdsPreviewRedeem(shares);
    mathint assets = defPsmUsdsInToGemOut(usdsOutSUsds, tout_);
    mathint daiInPsm = defPsmGemOutToUsdsIn(assets, tout_);

    // Contracts set up
    require usds.allowance(currentContract, psmWrap) == max_uint256;

    // ERC20 correct behaviour
    require usdc.totalSupply() >= usdc.balanceOf(receiver) + usdc.balanceOf(currentContract) + usdc.balanceOf(psmWrap) + usdc.balanceOf(psm) + usdc.balanceOf(psm.pocket());
    require dai.totalSupply() >= dai.balanceOf(psmWrap) + dai.balanceOf(psm);
    require usds.totalSupply() >= usds.balanceOf(currentContract) + usds.balanceOf(psmWrap) + usds.balanceOf(susds);
    require susds.totalSupply() >= susds.balanceOf(currentContract);
    require totalSupply() >= balanceOf(owner);

    // Behavior coming from deposit/mint functions
    require susds.balanceOf(currentContract) >= totalSupply();

    // Correct behaviour susds
    require usds.balanceOf(susds) >= susds.totalSupply() * susds.chi() / RAY();

    // Setup assumptions
    require usdc.allowance(pocket, psm) == max_uint256;
    require dai.allowance(psmWrap, psm) == max_uint256;

    // Avoid external contracts overflows
    require shares * susds.chi() <= max_uint256;
    require WAD() + tout_ <= max_uint256;
    require dai.totalSupply() + daiInPsm <= max_uint256;

    redeem@withrevert(e, shares, receiver, owner, minAssets);

    bool revert1 = e.msg.value > 0;
    bool revert2 = tout_ == max_uint256;
    bool revert3 = shares > balanceOfOwner;
    bool revert4 = assets < minAssets;
    bool revert5 = e.msg.sender != owner && allowanceOwnerSender < shares;
    bool revert6 = usdcBalanceOfPocket < assets;

    assert lastReverted <=> revert1 || revert2 || revert3 ||
                            revert4 || revert5 || revert6, "Revert rules failed";
}

// Verify correct storage changes for non reverting exit
rule exit(uint256 shares, address receiver, address owner) {
    env e;

    address other;
    require other != owner;

    mathint usdsOutSUsds = defSusdsPreviewRedeem(shares);

    mathint totalSupplyBefore = totalSupply();
    mathint balanceOfOwnerBefore = balanceOf(owner);
    mathint balanceOfOtherBefore = balanceOf(other);
    mathint susdsBalanceOfVaultBefore = susds.balanceOf(currentContract);
    mathint susdsBalanceOfReceiverBefore = susds.balanceOf(receiver);

    require totalSupplyBefore <= susdsBalanceOfVaultBefore;
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
