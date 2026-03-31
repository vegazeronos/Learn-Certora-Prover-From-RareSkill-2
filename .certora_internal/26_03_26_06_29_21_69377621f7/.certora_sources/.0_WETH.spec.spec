methods{
    function totalSupply() external returns uint256 envfree;
    function balanceOf(address owner) external returns uint256 envfree;
}

invariant token_integrity()
    nativeBalances[currentContract] >= totalSupply()
{
    preserved with (env e){
        require e.msg.sender != currentContract;
        require balanceOf(e.msg.sender) <= totalSupply();
    }
}