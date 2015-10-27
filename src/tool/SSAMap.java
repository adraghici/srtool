package tool;

import java.util.HashMap;
import java.util.Map;

public class SSAMap {
    private static final Integer DEFAULT_ID = 0;
    private final Map<String, Integer> nextID;

    public SSAMap() {
        this.nextID = new HashMap<>();
    }

    public int fresh(String var) {
        if (!nextID.containsKey(var)) {
            nextID.put(var, 0);
        } else {
            nextID.put(var, id(var) + 1);
        }
        return id(var);
    }

    private int id(String var) {
        return nextID.get(var);
    }
}
