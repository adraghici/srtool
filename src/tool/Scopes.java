package tool;

import java.util.*;

public class Scopes {
    private final IdMap idMap;
    private final Stack<Map<String, Integer>> scopes;

    /**
     * This will enter a default scope when created.
     */
    public Scopes() {
        idMap = new IdMap();
        scopes = new Stack<>();
        scopes.push(new HashMap<>());
    }

    public void enterScope() {
        scopes.add(new HashMap<>(scopes.peek()));
    }

    public void exitScope() {
        scopes.pop();
    }

    public void declareVar(String var) {
        scopes.peek().put(var, idMap.fresh(var));
    }

    public String getVar(String var) {
        return var + scopes.peek().get(var);
    }
}
