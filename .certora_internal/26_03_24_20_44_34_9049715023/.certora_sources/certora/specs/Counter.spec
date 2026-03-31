//TODO: Define ghost varible yang mau di track
ghost address ghost_owner;
ghost mathint ghost_counterBefore;
ghost mathint ghost_counterAfter; 

//TODO: define hook dari data yang mau di track
hook Sload address track_owner owner{
    ghost_owner = track_owner;
}
hook Sstore count uint256 counterAfter(uint256 counterBefore) {
    ghost_counterAfter = counterAfter;
    ghost_counterBefore = counterBefore;
}

//TODO: bikin rule 1. selain currentOwner, tidak dapat memanggil. dan currentOwner selalu sama dengna existingOwner
rule check_only_owner_can_call_function (method f, env e, calldataarg args){
    //precon
    resetCounter(e);
    address ownerBefore = ghost_owner;

    //action
    f(e,args);

    //postcon
    address ownerAfter = ghost_owner;

    //assert
    assert (ownerBefore == ownerAfter);
}

//TODO: bikin rule 2. increment hanya bisa dipanggil oleh owner, hasil counter sebelum +1 == counter sesudah
rule check_increment_always_add_one(method f, env e, calldataarg args){
    //precon
    require e.msg.value == 0;
    //action
    increment@withrevert(e);
    bool success = !lastReverted;
    //postcon
    mathint counterBefore = ghost_counterBefore;
    mathint counterAfter = ghost_counterAfter;
    address owner = ghost_owner;
    //assert
    assert(success <=> counterBefore + 1 == counterAfter && e.msg.sender == ghost_owner, "If and only if success, then counterBefore + 1 == counterAfter");
}