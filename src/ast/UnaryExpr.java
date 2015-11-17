package ast;

import com.google.common.collect.Lists;
import visitor.Visitor;

import java.util.List;
import java.util.Map;

public class UnaryExpr implements Expr {
    private final Expr atom;
    private final List<String> operators;

    public UnaryExpr(Expr atom, List<String> operators) {
        this.atom = atom;
        this.operators = operators;
    }

    public Expr getAtom() {
        return atom;
    }

    public List<String> getOperators() {
        return operators;
    }

    @Override
    public Object accept(Visitor visitor) {
        return visitor.visit(this);
    }

    @Override
    public Expr replace(Map<String, Expr> substitutes) {
        return new UnaryExpr(getAtom().replace(substitutes), Lists.newArrayList(operators));
    }
}
