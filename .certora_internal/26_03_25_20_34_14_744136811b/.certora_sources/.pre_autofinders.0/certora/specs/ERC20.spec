methods{
    function totalSupply() external returns uint256 envfree;
}

ghost mathint ghost_total_balances_all_address{
    init_state axiom ghost_total_balances_all_address == 0;
}

hook Sstore balanceOf[KEY address owner] uint256 newBalances(uint256 oldBalances){
    ghost_total_balances_all_address = ghost_total_balances_all_address + newBalances - oldBalances;
}

invariant check_solvency()
    ghost_total_balances_all_address == totalSupply();