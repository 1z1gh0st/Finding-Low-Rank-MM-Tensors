def flatten_index(i, j, num_cols):
    return (num_cols * i) + j

def unflatten_index(i, num_rows, num_cols):
    return ((i / num_rows), i % num_cols)

class MM_Scheme:
    def __init__(self, U: list, V: list, W: list):
        self.dimension = (len(U[0]), len(V[0]), len(U[0][0]))
        self.rank = max([len(U), len(V), len(W)])
        self.U = U
        self.V = V
        self.W = W

    def __str__(self):
        result = ""
        n = self.dimension[0]
        m = self.dimension[1]
        p = self.dimension[2]
        for index in range(max([n*m, m*p, n*p])):
            row = f"{unflatten_index(index)}:"
            result.append(row)
        return result
