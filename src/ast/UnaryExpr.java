package ast;

import com.google.common.collect.Lists;

import java.util.List;

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
    public List<Node> getChildren() {
        return Lists.newArrayList(atom);
    }
}
