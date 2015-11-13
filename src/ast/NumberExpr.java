package ast;

import visitor.Visitor;

public class NumberExpr implements AtomExpr {
    private final String number;

    public NumberExpr(String number) {
        this.number = number;
    }

    public String getNumber() {
        return number;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }
}
