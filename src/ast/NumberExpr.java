package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class NumberExpr implements AtomExpr {
    private final int number;

    public NumberExpr(int number) {
        this.number = number;
    }

    public int getNumber() {
        return number;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
