package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class UnaryExpr implements Expr {
    private final AtomExpr atom;
    private final List<String> operators;

    private UnaryExpr(AtomExpr atom, List<String> operators) {
        this.atom = atom;
        this.operators = operators;
    }

    private AtomExpr getAtom() {
        return atom;
    }

    private List<String> getOperators() {
        return operators;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(atom);
    }
}
