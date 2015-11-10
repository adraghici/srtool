package ast;

import com.google.common.collect.Lists;

import java.util.List;

public class NumberExpr implements AtomExpr {
    private final String number;

    public NumberExpr(String number) {
        this.number = number;
    }

    public String getNumber() {
        return number;
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
