methods {
    function totalVotes() external returns(uint256) envfree;
    function votesInFavor() external returns(uint256) envfree;
    function votesAgainst() external returns(uint256) envfree;
}

invariant totalVotesMatch()
    to_mathint(totalVotes()) == to_mathint(votesInFavor()) + to_mathint(votesAgainst());