method{
    function deposit() external payable;
    function withdraw() external;

    function balanceOf(address owner) external returns uint256 envfree;
    function totalSupply() external returns uint256 envfree;
}

//TODO: Deposit Success Verify WETH received == ETH Deposit 
rule deposit_success(env e, uint256 amount){
    //precon
    require e.msg.value == amount;
    require nativeBalances[e.msg.sender] >= amount;

    mathint wethSenderBefore = balanceOf(e.msg.sender);
    mathint balanceSenderBefore = nativeBalances[e.msg.sender];

    //action
    deposit(e);

    //poststate
    mathint wethSenderAfter = balanceOf(e.msg.sender);
    mathint balanceSenderAfter = nativeBalances[e.msg.sender];

    //assert
    assert balanceSenderBefore - amount = balanceSenderAfter;
    assert wethSenderBefore + amount = wethSenderAfter;
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
//TODO: Withdraw Revert
//TODO: Verify TotalSupply <= ETH Held by contract
//TODO: no other user balance affected
//TODO: Only owner and spender can change the balance 
//TODO: create the invariant for this WETH