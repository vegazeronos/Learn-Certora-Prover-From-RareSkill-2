methods{
    function transfer(address to, uint256 amount) external returns bool envfree;
    function balanceOf(address account) external returns uint256 envfree;
}

//TODO: verify the transfer is intended
rule check_transfer_success(address to, uint256 amount, env e){
    //precon
    require e.msg.value == 0;
    require balanceOf(e.msg.sender) + balanceOf(to) <= max_uint256;
    mathint balanceSenderBefore = balanceOf(e.msg.sender);
    mathint balanceReceiverBefore = balanceOf(to);

    //action
    transfer(e,to, amount);

    //poststate
    mathint balanceSenderAfter = balanceOf(e.msg.sender);
    mathint balanceReceiverAfter = balanceOf(to);

    //assert
    if(receiver != e.msg.sender){
        assert balanceSenderAfter == balanceSenderBefore - amount;
        assert balanceReceiverAfter == balanceReceiverBefore + amount;
    }else{
        assert balanceSenderAfter == balanceSenderBefore;
        assert balanceReceiverAfter == balanceReceiverBefore;
    }
    
}

//TODO: verify the transfer revert because of 
rule check_transfer_revert(env e, address to, uint256 amount){
    //precon
    //action
    transfer@withrevert(e,to, amount);
    bool reverted = lastReverted;
    //poststate
    //assert
    assert reverted <=> (e.msg.value > 0 || amount > balanceOf(e.msg.sender));
}