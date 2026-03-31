//TODO: track the increment times ==> count before + increment times == count after

ghost mathint ghost_track_increment;

hook Sstore count uint256 countAfter(uint256 countBefore){
    ghost_track_increment = ghost_track_increment +1;
}

methods {
    function increment() external envfree;
    function count() external returns uint256 envfree;
}

rule check_increment_track_right(){
    //precon
    require (ghost_track_increment == 0, "should be start with 0");
    mathint countBefore = count();
    //action
    increment();
    increment();
    increment();
    increment();
    increment();
    increment();
    increment();

    //postcon
    mathint countAfter = count();

    assert (countAfter == countBefore + ghost_track_increment, "the count tracker is not right");



}