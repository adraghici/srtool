package ast;

import visitor.Visitor;

import java.util.Map;

public class ResultExpr implements AtomExpr {
    private final String token;

    public ResultExpr(String token) {
        this.token = token;
    }

    public String getToken() {
        return token;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> vars) {
        return vars.get(token);
    }
}
