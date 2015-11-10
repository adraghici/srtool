package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class ParenExpr implements AtomExpr {
    private final AtomExpr atom;

    public ParenExpr(AtomExpr atom) {
        this.atom = atom;
    }

    private AtomExpr getAtom() {
        return atom;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList(atom);
    }
}
