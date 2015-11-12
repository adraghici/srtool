package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

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
    public Set<String> getModset() {
        return Sets.newHashSet();
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(atom);
    }
}
