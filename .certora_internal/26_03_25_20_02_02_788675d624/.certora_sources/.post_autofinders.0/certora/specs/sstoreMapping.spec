//TODO: want to check totalPoints == all points across all user
ghost mathint ghost_total_all_points;
ghost mathint ghost_total_all_points_invariants;

hook Sstore pointsOf[KEY address owner] mathint newBalance(mathint oldBalance){
    ghost_total_all_points = ghost_total_all_points + newBalance - oldBalance;
    ghost_total_all_points_invariants = ghost_total_all_points + newBalance - oldBalance;
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
    ghost_total_all_points_invariants == totalPoints();

