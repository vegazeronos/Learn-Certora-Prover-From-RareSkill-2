//TODO: want to check totalPoints == all points across all user
methods{
    function totalPoints() external returns uint256 envfree;
}

ghost mathint ghost_total_all_points{
    init_state axiom ghost_total_all_points == 0;
}

hook Sstore pointsOf[KEY address owner] uint256 newBalance(uint256 oldBalance){
    ghost_total_all_points = ghost_total_all_points + newBalance - oldBalance;
}

hook Sload uint256 balances pointsOf[KEY address owner]{
    require ghost_total_all_points >= balances;
}

rule check_total_point_acroos_all_user_is_correct (method f, env e, calldataarg args){
    //precon
    require ghost_total_all_points == 0 && totalPoints() == 0;
    //action
    f(e, args);
    //postcon
    //assert
    assert ghost_total_all_points == totalPoints();
}

invariant check_total_point_acroos_all_user_is_correct_invariant()
    ghost_total_all_points == totalPoints();

