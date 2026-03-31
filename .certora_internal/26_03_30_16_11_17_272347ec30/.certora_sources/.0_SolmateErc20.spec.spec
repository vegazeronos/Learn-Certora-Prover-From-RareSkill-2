methods{
    function transfer(address to, uint256 amount) external returns bool;
    function transferFrom(address from, address to, uint256 amount) external returns bool;
    function approve(address spender, uint256 amount) external returns bool;
    function mint(address _to, uint256 _amount) external;

    function balanceOf(address account) external returns uint256 envfree;
    function allowance(address from, address to) external returns uint256 envfree;
    function totalSupply() external returns uint256 envfree;
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
    if(to != e.msg.sender){
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
    mathint senderBalance = balanceOf(e.msg.sender);
    //action
    transfer@withrevert(e, to, amount);
    bool reverted = lastReverted;
    //poststate
    //assert
    assert reverted <=> (e.msg.value > 0 || amount > senderBalance);
}


// TODO: verify transferFrom success, receiver balance +, allowance -, benificiaryBalance -, require apporval from benif to msg.sender
rule check_transfer_from_success(env e, address from, address to, uint256 amount){
    //precon
    require allowance(from, e.msg.sender) == amount && amount != max_uint256;
    require e.msg.sender != to && e.msg.sender != from;
    require balanceOf(from) + balanceOf(to) <= max_uint256;
    mathint balanceFromBefore = balanceOf(from);
    mathint balanceToBefore = balanceOf(to);
    mathint balanceSenderBefore = balanceOf(e.msg.sender);
    mathint allowanceBefore = allowance(from, e.msg.sender);

    //action
    transferFrom(e,from, to, amount);

    //poststate
    mathint balanceFromAfter = balanceOf(from);
    mathint balanceToAfter = balanceOf(to);
    mathint balanceSenderAfter = balanceOf(e.msg.sender);
    mathint allowanceAfter = allowance(from, e.msg.sender);

    //assert
    if(from != to){
        assert balanceFromAfter == balanceFromBefore - amount; // from send balances
        assert balanceToAfter == balanceToBefore + amount; // to receive more balances
        assert balanceSenderBefore == balanceSenderAfter; //no change
        assert allowanceAfter == allowanceBefore - amount;
    }else{
        assert balanceFromAfter == balanceFromBefore; // no change
        assert balanceToAfter == balanceToBefore; // no change
        assert balanceSenderBefore == balanceSenderAfter; //no change
        assert allowanceAfter == allowanceBefore - amount;
    }
}

// TODO: verify transferFrom revert, approval not suff, balance benif not suff, eth sent
rule check_transfer_from_revert(env e, address from, address to, uint256 amount){
    //precon
    mathint approvalSender = allowance(from, e.msg.sender);
    mathint balanceFrom = balanceOf(from);
    //action
    transferFrom@withrevert(e, from, to, amount);
    bool reverted = lastReverted;
    //post state
    //assert
    assert reverted <=> (
            approvalSender < amount || 
            balanceFrom < amount || 
            e.msg.value > 0
        );
}


//TODO: check change in allowance
rule check_change_allowance(env e, address from, address to, uint256 amount){
    //precon
    // require allowance(from, e.msg.sender) <= amount;
    mathint allowanceSenderBefore = allowance(from, e.msg.sender);

    //action
    transferFrom(e, from, to, amount);

    //post state
    mathint allowanceSenderAfter = allowance(from, e.msg.sender);

    //assert
    if(allowanceSenderBefore == max_uint256){
        assert allowanceSenderAfter == max_uint256;
    }else{
        assert allowanceSenderAfter == allowanceSenderBefore - amount;
    }
}

//TODO: prove that approval make change of the allowance
rule check_approve(address to, uint256 amount, env e){
    //precon
    // mathint allowanceSenderBefore = allowance(e.msg.sender, to);

    //action
    approve@withrevert(e, to, amount);
    bool reverted = lastReverted;

    //poststate
    mathint allowanceSenderAfter = allowance(e.msg.sender, to);

    //assert
    assert !reverted => allowanceSenderAfter == amount;
    assert reverted <=> e.msg.value != 0;
}

rule check_return_true(calldataarg args, env e){
    //TODO check return true transfer
    bool transferSuccess = transfer@withrevert(e, args);
    bool transferReverted = lastReverted;

    //TODO check return true transferFrom
    bool transferFromSuccess = transferFrom@withrevert(e, args);
    bool transferFromReverted = lastReverted;

    //TODO check return true approve
    bool approveSuccess = approve@withrevert(e,args);
    bool approveReverted = lastReverted;

    assert !transferReverted => transferSuccess == true;
    assert !transferFromReverted => transferFromSuccess == true;
    assert !approveReverted => approveSuccess == true;
}

rule check_return_true_transfer(calldataarg args, env e){
    //TODO check return true transfer
    bool transferSuccess = transfer@withrevert(e, args);
    bool transferReverted = lastReverted;

    assert !transferReverted => transferSuccess == true;
}
rule check_return_true_transferFrom(calldataarg args, env e){
    //TODO check return true transferFrom
    bool transferFromSuccess = transferFrom@withrevert(e, args);
    bool transferFromReverted = lastReverted;

    assert !transferFromReverted => transferFromSuccess == true;
}
rule check_return_true_approve(calldataarg args, env e){
    //TODO check return true approve
    bool approveSuccess = approve@withrevert(e,args);
    bool approveReverted = lastReverted;

    assert !approveReverted => approveSuccess == true;
}


//TODO prove mint only effect the receiver address + totalsupply, no other can gain it
rule check_mint_success(env e, address to, uint256 amount){
    //precon
    require totalSupply() >= balanceOf(to);
    mathint balanceToBefore = balanceOf(to);
    mathint totalSupplyBefore = totalSupply();

    //action
    mint@withrevert(e, to, amount);
    bool reverted = lastReverted;

    //poststate
    mathint balanceToAfter = balanceOf(to);
    mathint totalSupplyAfter = totalSupply();

    //assert
    assert !reverted <=> (
        (totalSupplyAfter == totalSupplyBefore + amount) && 
        (balanceToAfter == balanceToBefore + amount)
        );
    assert reverted <=> (
        e.msg.value != 0 ||
        totalSupplyBefore + amount > max_uint256;
        );
}