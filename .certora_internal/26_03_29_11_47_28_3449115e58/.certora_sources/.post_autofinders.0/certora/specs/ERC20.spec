methods{
    function totalSupply() external returns uint256 envfree;
    function balanceOf(address) external returns uint256 envfree;
}

ghost mathint ghost_total_balances_all_address{
    init_state axiom ghost_total_balances_all_address == 0;
}

hook Sload uint256 balance balanceOf[KEY address owner]{
    require to_mathint(balance) <= ghost_total_balances_all_address;
}

hook Sstore balanceOf[KEY address owner] uint256 newBalances(uint256 oldBalances){
    ghost_total_balances_all_address = ghost_total_balances_all_address + newBalances - oldBalances;
}

invariant check_solvency()
    ghost_total_balances_all_address == to_mathint(totalSupply());


//TODO: make rule to check how transfer goes, prove it

rule check_transfer(env e){
    requireInvariant check_solvency();
    
    mathint amount;
    address to;

    //precon
    require e.msg.sender != currentContract;
    require e.msg.sender != to;

    mathint balanceSenderBefore = balanceOf(e.msg.sender);
    mathint balanceReceiverBefore = balanceOf(to);
    mathint totalSupplyBefore = totalSupply();

    //action
    transfer(e,to,amount);

    //post state
    mathint balanceSenderAfter = balanceOf(e.msg.sender) - amount;
    mathint balanceReceiverAfter = balanceOf(to) + amount;
    mathint totalSupplyAfter = totalSupply();

    //assert
    assert balanceReceiverAfter == balanceReceiverBefore + amount;
    assert balanceSenderAfter == balanceSenderBefore + amount;
    assert totalSupplyBefore == totalSupplyAfter ;
}