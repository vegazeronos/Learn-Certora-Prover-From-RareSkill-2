methods{
    function votesInFavor() external returns uint256 envfree;
    function votesAgainst() external returns uint256 envfree;
}

ghost mathint ghostTotalVotes{
    init_state axiom ghostTotalVotes == 0;
}

hook Sstore hasVoted[KEY address owner] bool newStatus(bool oldStatus){
    ghostTotalVotes = ghostTotalVotes + 1;
}

invariant check_totalVotes_equal_all_votes()
    ghostTotalVotes == votesInFavor() + votesAgainst();