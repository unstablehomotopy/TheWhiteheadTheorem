from PIL import Image, ImageDraw
from PIL import ImageFont
from math import *

def index(list):
    return range(len(list))


class vector:
    def __init__(self, entries):
        self.entries = entries
        self.length = len(entries)

    def __getitem__(self, i):
        return self.entries[i]

    def __add__(self, other):
        entries = []
        for i in range(len(self.entries)):
            entries.append(self[i] + other[i])
        return vector(entries)

    def __rmul__(self, a):
        entries = []
        for i in range(len(self.entries)):
            entries.append(a*self[i])
        return vector(entries)

    def height(self):
        return self.entries[1] - self.entries[0]

    def average(self):
        (1/float(len(self.entries)))*sum([self.entries])

    def print(self):
        print(self.entries)


def exp(theta):
    return vector([cos(theta), sin(theta)])


def interpolation(t):
    if 0 <= t and t <= 0.5:
        return 0.5 - sqrt(0.25-t*t)
    if 0.5 < t <= 1:
        s = 1-t
        return 0.5 + sqrt(0.25-s*s)
    return (-2.77333)*t*t*t + 4.16*t*t + (-0.386667)*t


def curve(coordinates, border):
    for counter in range(len(coordinates) - 1):
        a = coordinates[counter][0]
        b = coordinates[counter+1][0]
        i = coordinates[counter][1]
        j = coordinates[counter+1][1]
        draw.line((j, b, i, a), fill=(256, 256, 256), width=12) 
        draw.line((j, b, i, a), fill=(0, 0, 0), width=4)
    image.save('test.png')      


def squiggle(v1, v2, border):
    coordinates = []
    l = 100
    for r in range(l):
        t = float(r)/l
        s = interpolation(t)
        x = s*v1[0] + (1-s)*v2[0]
        y = t*v1[1] + (1-t)*v2[1]
        coordinates.append([x, y])
    curve(coordinates, border)


def arc(v, r, theta1, theta2, u, border):
    n = floor((theta2 - theta1)*300)
    coordinates = []
    for i in range(n):
        t = float(float(i) * (theta2 - theta1)) / float(n)
        if u ==0:
            w = v +(-1)* r*exp(t)
        if u == 1:
            w = v + r*exp(t)          
        coordinates.append(w)
    curve(coordinates, border)


def bubble(v, color):
    draw.ellipse((v[1]-13, v[0]-13, v[1]+13, v[0]+13), fill = (0,0 ,0))
    draw.ellipse((v[1]-10, v[0]-10, v[1]+10, v[0]+10), fill = color)


class cell:
    def __init__(self, entries, border, bubble, color):
        self.symbol = None
        self.entries = entries
        self.border = border
        self.x1    = entries[0]
        self.y11   = entries[1]
        self.y12   = entries[2]
        self.x2    = entries[0] +1
        self.y21   = entries[3]
        self.y22   = entries[4]
        self.y1 = self.y12 - self.y11
        self.y2 = self.y22 - self.y21
        self.width = 1
        self.bubble = bubble
        self.color = color

    def print(self):
        print("x1: ", self.x1)
        print("y11: ", self.y11)
        print("y12: ", self.y12)
        print("x2: ", self.x2)
        print("y21: ", self.y21)
        print("y22: ", self.y22)

    def copy(self):
        x1 = self.x1
        y11 = self.y11
        y12 = self.y12
        y21 = self.y21
        y22 = self.y22
        border = self.border
        bubble = self.bubble
        color = self.color
        return cell([x1, y11, y12, y21, y22], border, bubble, color)

def copy_cell(l):
    cells = []
    for c in l:
        d = c.copy()
        cells.append(d)
    return cells


def xshift(c, t):
    x1 = c.x1 + t
    x2 = c.x2 + t
    y11 = c.y11
    y12 = c.y12
    y21 = c.y21
    y22 = c.y22
    border = c.border
    bubble = c.bubble
    color = c.color
    return cell([x1, y11, y12, y21, y22], border, bubble, color)


def yshift(c, y1, y2):
    y11 = c.y11 + y1
    y12 = c.y12 + y1
    y21 = c.y21 + y2
    y22 = c.y22 + y2
    x1 = c.x1
    border = c.border
    bubble = c.bubble
    color = c.color
    return cell([x1, y11, y12, y21, y22], border, bubble, color)


class diagram:
    def __init__(self, heights, cells):
        self.color = color
        self.heights = heights
        self.width = len(heights)
        self.height = 0
        for h in self.heights:
            if h > self.height:
                self.height = h
        self.height = self.height
        self.cells = cells


    def __mul__(self, other):
        assert self.heights[-1] == other.heights[0]

        heights = self.heights[0:-1].copy() + other.heights.copy()

        cells = copy_cell(self.cells)
        for cell in copy_cell(other.cells):
            cells.append(xshift(cell, self.width - 1))

        return diagram(heights, cells)


    def __add__(self, other):
        cells = self.cells.copy()
        for i in range(len(other.cells)):
            x1 = other.cells[i].x1
            x2 = other.cells[i].x2
            h1 = self.heights[x1]
            h2 = self.heights[x2]
            cells.append(yshift(other.cells[i], h1, h2))
        p = len(self.heights)
        return diagram([self.heights[i] + other.heights[i] for i in range(p)], cells)


    def coordinate(self, v, unit,  W, H):
        h = unit*self.heights[v[0]]
        w = unit*self.width
        x = unit*float(v[0])
        y = unit*float(v[1])
        a = H/2-h/2 + unit*v[1]
        b = W/2-w/2 + unit*v[0] + unit/2
        return vector([a, b])


    def print(self, unit = 110, border = 0, radius = 10):
        global image
        W = unit*self.width + 100
        H = unit*self.height + 100
        image = Image.new('RGBA', (W, H), (256,256,256))
        global draw
        draw = ImageDraw.Draw(image)
        for cell in self.cells:
            v11 = self.coordinate(vector([cell.x1, cell.y11]), unit, W, H)
            v12 = self.coordinate(vector([cell.x2, cell.y21]), unit, W, H)
            v21 = self.coordinate(vector([cell.x1, cell.y12]), unit, W, H)
            v22 = self.coordinate(vector([cell.x2, cell.y22]), unit, W, H)
            m1 = (1/2)*(v11 + v21)
            m2 = (1/2)*(v12 + v22)
            o = (1/2)*(m1 + m2)

            if cell.y1 == 0 and cell.y2 == 1:
                squiggle(m1, o, cell.border) 
                if cell.bubble == 1:
                    bubble(o, self.color)
                image.save('test.png')

            if cell.y1 == 0 and cell.y2 == 2:

                arc(m2, unit/2, -0.05, pi+0.05, 0, cell.border)
                if cell.bubble == 1:
                    bubble(o, cell.color)
                image.save('test.png')

            if cell.y1 == 1 and cell.y2 == 0:
                squiggle(o, m2, cell.border)
                if cell.bubble == 1:
                    bubble(o, cell.color)
                image.save('test.png')

            if cell.y1 == 1 and cell.y2 == 1:
                squiggle(m1, m2, cell.border)
                if cell.bubble == 1:
                    bubble(o, cell.color)
                image.save('test.png')

            if cell.y1 == 1 and cell.y2 == 2:
                a = (1/4)*(3*v22 + v12)
                b = (1/4)*(v22 + 3*v12)
                squiggle(o, a, cell.border)
                squiggle(o, b, cell.border)
                squiggle(m1, o, cell.border)
                p = vector([o[0], o[1]])
                if cell.bubble == 1:
                    bubble(p, cell.color)
                image.save('test.png')

            if cell.y1 == 2 and cell.y2 == 0:
                arc(m1, unit/2, -0.05, pi+0.05, 1, cell.border)
                if cell.bubble == 1:
                    bubble(o, cell.color)
                image.save('test.png')

            if cell.y1 == 2 and cell.y2 == 1:
                a = (1/4)*(3*v21 + v11)
                b = (1/4)*(v21 + 3*v11)
                squiggle(a, o, cell.border)
                squiggle(b, o, cell.border)
                squiggle(o, m2, cell.border)
                p = vector([o[0], o[1]])
                if cell.bubble == 1:
                    bubble(p, cell.color)
                image.save('test.png')

            if cell.y1 == 2 and cell.y2 == 2:
                w11 = (1/2)*(v11 + m1)
                w12 = (1/2)*(v12 + m2)
                w21 = (1/2)*(v21 + m1)
                w22 = (1/2)*(v22 + m2)
                if cell.border == 1:
                    squiggle(w12, w21, 1)
                    squiggle(w11, w22, 1)
                if cell.border == 2:
                    squiggle(w11, w22, 1)
                    squiggle(w12, w21, 1)
                if cell.bubble == 1:
                    bubble(o, cell.color)
                image.save('test.png')


def make_cell(i, j, color =(0, 0, 0), border = 1, bubble =0):
    return diagram([i, j], [cell([0, 0, i, 0, j], border, bubble, color)])   


blue = (102, 178, 255)
green = (0, 204, 102)
yellow = (250, 250, 50)
brown = (30, 150, 69)
color = blue

John = make_cell(4, 0, green, 1, 0)
counit = make_cell(2, 0, blue,1, 0)
unit = make_cell(0, 2, blue, 1, 0)
C = make_cell(2, 0, green,1, 1)
D = make_cell(2,1,yellow, 1,1)
unitwithbubble = make_cell(0, 2, blue, 1, 1)
Unit = make_cell(0, 1, blue, 1, 0)
Counit = make_cell(1, 0, blue, 1, 0)
Multiplication = make_cell(2, 1, blue, 1, 0)
Multiplicationwithbubble = make_cell(2, 1, blue, 1, 1)
Comultiplication = make_cell(1, 2, blue, 0, 0)
IdF = make_cell(1, 1, blue, 1, 1)
IdG = make_cell(1, 1, blue, 1, 0)
identity = make_cell(1, 1, blue, 0, 0)
justamap = make_cell(1, 1, green, 1, 1)
Ltriangle = (unit + IdG)*(IdF + counit)
Rtriangle = (IdG + unit)*(counit + IdF)
Lbraid = make_cell(2, 2, blue, 1, 0)
Rbraid = make_cell(2, 2, blue, 2, 0)
a1 = unit+identity+identity
a2 = identity + counit +identity
a3 = unit + identity+identity
a4 = identity + identity + counit
(Comultiplication*(Comultiplication+identity)).print()


