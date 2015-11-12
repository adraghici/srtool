package ast;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;

public class NumberExpr implements AtomExpr {
    private final String number;

    public NumberExpr(String number) {
        this.number = number;
    }

    public String getNumber() {
        return number;
    }

    @Override
    public Set<String> getModset() {
        return Sets.newHashSet();
    }

    @Override
    public List<Node> getChildren() {
        return Lists.newArrayList();
    }
}
