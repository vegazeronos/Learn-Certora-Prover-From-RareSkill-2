methods{
    function deposit() external;
    function withdraw() external;

    function balanceOf(address owner) external returns uint256 envfree;
    function totalSupply() external returns uint256 envfree;
}

persistent ghost bool g_callFailed;

hook CALL (uint gas, address to, uint value, uint argsOffset, uint argsLength, uint retOffset, uint retLength) uint rc{
    if(rc == 0){
        g_callFailed = true;
    }else {
        g_callFailed = false;
    }
}

//TODO: Deposit Success Verify WETH received == ETH Deposit , increase totalsyupply
rule deposit_success(env e, uint256 amount){
    //precon
    require e.msg.sender != currentContract;
    require e.msg.value == amount;
    require nativeBalances[e.msg.sender] >= amount;
    require balanceOf(e.msg.sender) + amount < max_uint256;

    mathint wethSenderBefore = balanceOf(e.msg.sender);
    mathint balanceSenderBefore = nativeBalances[e.msg.sender];
    mathint totalSupplyBefore = totalSupply();

    //action
    deposit(e);

    //poststate
    mathint wethSenderAfter = balanceOf(e.msg.sender);
    mathint balanceSenderAfter = nativeBalances[e.msg.sender];
    mathint totalSupplyAfter = totalSupply();

    //assert
    assert balanceSenderBefore - amount == balanceSenderAfter;
    assert wethSenderBefore + amount == wethSenderAfter;
    assert totalSupplyBefore + amount == totalSupplyAfter;
}

//TODO: Deposit Revert -> revert ketika dana tidak cukup atau weth nyentuh max256
rule deposit_revert(env e, uint256 amount){
    require e.msg.value == amount;
    mathint balanceSender = nativeBalances[e.msg.sender];
    
    deposit@withrevert(e);
    bool reverted = lastReverted;

    assert reverted => (
        balanceSender < amount ||
        to_mathint(totalSupply()) + amount > max_uint256 
    );
}


//TODO: Withdraw Success Verify ETH received == WETH withdrawed
rule withdraw_success(env e, uint256 amount){
    //precon
    require e.msg.sender != currentContract;
    require balanceOf(e.msg.sender) - amount < 0;

    mathint ethBefore = nativeBalances[e.msg.sender];
    mathint wethBefore = balanceOf(e.msg.sender);
    mathint totalSupplyBefore = totalSupply();

    //action
    withdraw@withrevert(e, amount);
    bool reverted = lastReverted;

    //postcon
    mathint ethAfter = nativeBalances[e.msg.sender];
    mathint wethAfter = balanceOf(e.msg.sender);
    mathint totalSupplyAfter = totalSupply();

    //assert balance eth +, balance weth -, totalsupply -
    assert !reverted => (
        ethBefore + amount == ethAfter ||
        wethBefore - amount == wethAfter ||
        totalSupplyBefore - amount == totalSupplyAfter
    );
}

//TODO: Withdraw Revert wethBalance < amount, 
rule withdraw_revert(env e, uint256 amount){
    mathint wethBalance = balanceOf(e.msg.sender);

    withdraw@withrevert(e, amount);
    bool reverted = lastReverted;

    assert reverted <=> (
        wethBalance < amount ||
        e.msg.value != 0 ||
        g_callFailed 
    );
}

//TODO: Verify TotalSupply <= ETH Held by contract
//TODO: Verify TotalETH Deposits >= WETH total supply
