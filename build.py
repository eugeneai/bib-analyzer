#encoding:utf-8
# pip install python-Levenshtein
XHTML_NS = 'http://www.w3.org/1999/xhtml'
from lxml import html, etree as et
import Levenshtein
import networkx as nx
import itertools

l2r_oneway = { "JI":'Л', 'J|':'Л', 'JL':'Л' }
l2r = { 'a':'а', 'c':'с', 'e':'е', 'k':'к', 'o':'о', 'p':'р', 'u':'и', 'x':'х', 'y':'у',\
        'A':'А', 'B':'В', 'C':'С', 'E':'Е', 'H':'Н', 'K':'К', 'O':'О', 'P':'Р', 'X':'Х', 'Y':'У' }
r2l = {}
for i in l2r: r2l[ l2r[i] ] = i; # swapping key-values
wrong_words = [ 'Атлас', 'Inform', 'Исслед', 'Publ', 'Proc', 'Guidance', 'Suppl', 'Sci', 'Space', 'Notices',\
                'Paper', 'www', 'html', 'Монография', 'ред', 'Lett', 'pp', 'англ', 'журнал', 'Journ', 'Machine', 'Algorithm', \
                'Photometry', 'тез', 'гос', 'Известия', 'вузов', 'Astrophys', 'СССР', 'изд', 'СПб', 'Optical', 'докл', 'Тез', \
                'January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'November', 'December', \
                'Цupkyляp', 'Навигации', 'Univ', 'Pub', 'Труды', 'Chicago', 'Наука', 'Случайные', 'Тезисы', 'Журнал', 'Symp', \
                'Not', 'Geophys', 'Aerosp', 'Tech', 'Geophys', 'Galaxy', 'Прикладная', 'ВУЗов', 'et', 'al', 'пособие', 'Вестник', \
                'Машиностроение', 'Стр', 'Wash.', 'Ca.', 'Control', 'IX', 'ХI', 'ХХ', 'IV', 'VI', 'II', 'радио', 'Радио', \
                'Сов.', 'Япония', 'France', 'Germany', "Moscow", "Processing Data.", 'Материал', "конф Тр.", "Тр. конф", "its", \
                "Applications", "Nuovo Cim.", 'ил.', 'физ.', 'It.', 'Trans.', 'IEEE', 'J-', 'Acta.', 'Acad.', 'Astron', 'inc', \
                'Inc', 'INC', 'т.', 'доп.', 'перераб', 'Высш.', 'шк.', 'El.', 'Еl.', 'EL.', "IRE", 'Analysis', 'Image', 'Шк.', \
                'школа', 'МИРЭА', 'исправл', 'АОЭ', "науч.", "Сб.", "Материалы", "междунар", "Conf AIP.", "Conf", "Eds S.", "Eds.", \
                "Eds", "Press", "AIP", "журн.", "журн", "Опт.", "Петербург", "С.Петербург", "Космич.", "Nucl Phys.", "Phys.", \
                "Ed.", "Тр.", "Pointing", "in Proce.", "Ann Rev.", "Rev.", "им.", "ИПМ" ]

split_words = [' and ', ' And ', 'и др.', 'М.:', 'et al.', 'et all.', 'Под. ред.', 'Под ред.', '. —', '//', '/', ', ', ',']

r2l_translit = { 'а':'a', 'б':'b', 'в':'v', 'г':'g', 'д':'d', 'е':'e', 'ё':'yo', 'ж':'jh', 'з':'z',\
        'и':'i', 'й':'y', 'к':'k', 'л':'l', 'м':'m', 'н':'n', 'о':'o', 'п':'p', 'р':'r',\
        'с':'s', 'т':'t', 'у':'u', 'ф':'f', 'х':'h', 'ц':'ts', 'ч':'ch', 'ш':'ch', 'щ':'sh',\
        'ъ':'', 'ы':'y', 'ь':'', 'э':'e', 'ю':'u', 'я':'ya' }

books_counter = 0
authors_counter = 0

def mark_book_fields( book_txt ):
  # Kornus K., Lehner M., Schroeder M. Geometric Inflight Calibration of the Stereoscopic CCD-Linescanner // MOMS-2P, ISPRS Com I Symp., Bangalore. 1998. Vol. XXXII-1. P. 148-155.
  # Roeser, S. And Bastian, U., 1991. &quot;PPM Star Catalogue&quot;. Astronomisches Rechen-1.stitut, Heidelberg. Spectrum Akademischer Verlag. Heidelberg.
  # Высокоскоростной алгоритм сегментации изображений звездного неба, полученных от датчиков сканерного типа / Д.Ю. Пашенцев и др. // Цифровая обработка сигналов: научно-технический журнал. 2011. №3. С. 42-46.
  btmp = str(book_txt)
  for w in split_words: btmp = btmp.replace( w, '|' )
  # Срастить несколько потенциальных имён-фамилий
  # заменить точки на |
  # заменить подстроки |Asdasd|A.|B.| на |Asdasd|A.|B.|
  # заменить подстроки |Asdasd|A.|B.| на |AsdasdA.|B.|
  # заменить подстроки |Asdasd|A.B.| на |AsdasdA.B.|
  # заменить подстроки |Asdasd|A.| на |AsdasdA.|
  # заменить подстроки |A.|A.|Asdasd| на |A.|AsdasdA.|
  # заменить подстроки |A.|Asdasd| на |AsdasdA.|
  fields = btmp.split('|')
  fields = [ f.strip(' ') for f in fields if len(f)>0 ]
  return fields

def get_book_year( fields ):
  # Определение года публикации
  for fld in fields:
    for i in range(4,len(fld)+1):
      d = fld[i-4:i]
      if d.isdigit() and 1900<int(d)<2016:
        return d
  return ""

def book2authors( fields ):
      authors_list = []
      # Простой вылов соавторов
      for fld in fields:
        # Нахождение максимального количества соавторов
        # Попытка поймать фамилию если она в начале поля: |Плахов Ю.В. Геодезическая астрономия...|
        #                                                 |Lander J., Powell Т., Cox J. Orbit Determination and ...|
        fs = fld.split(' ') # fld.replace('. ',' ')
        if len(fs)>2 and 1<len(fs[0])<16 and fs[1].count('.') > 0:
          if len(fs[2])<3 and fs[2].count('.') > 0: fld = ' '.join(fs[0:3])
          else: fld = ' '.join(fs[0:2])

        # Оставляем только короткие поля содержащие 1..2 точки
        if not( 2<len(fld)<20 and 0<fld.count('.')<4 ): continue;
        if len([ '1' for c in fld if c in '0123456789:()' ])>0: continue; # комбинации с числами
        # Слова которые не должны считаться фамилиями
        fd = fld.replace(' ','.').split('.')
        # 
        if len( [ '1' for w in wrong_words if w in fd or (w[-1]=='.' and w[:-1] in fd)] )>0: continue;
        a_tmp = fld.replace('. ','.')
        while a_tmp[0] == ' ': a_tmp = a_tmp[1:] # Удалить пробелы в начале
        while a_tmp[-1] == ' ': a_tmp = a_tmp[:-1] # Удалить пробелы в конце
        a_tmp = a_tmp.replace("'", '')
        if len(a_tmp) < 3 or a_tmp in authors_list: continue;
        authors_list.append( a_tmp )

      # Переставить фамилию вперёд, инициалы -- в конец
      authors = []
      for a in authors_list:
        ax = a.replace(' ','.').split('.')
        s = ''
        for x in ax: # Находим самое длинное поле
          if len(x) > len(s): s = x;
        if len(s) == 1 : continue; # Фамилия не может быть длиной в одну букву, это ошибка
        s_out = s + ' ' + ''.join( x + '.' for x in ax if len(x)>0 and x!=s )
        s_out1, lang = localize( s_out ) # локализовать имя автора
        authors.append( s_out1 )

      return authors


def short_name( name_str ):
  ls = name_str.split(' ')
  if len(ls) < 2: name = name_str
  elif '.' in name_str: name = name_str
  else:
    ls = name_str.split(' ')
    name = ls[0] + ' ' + ls[1][0] + '.' # ФИ
    if len(ls)>2: name = name + ls[2][0] + '.' # О
  return name

def name2key( name_str ):
  global keys_equi
  key = name_str.lower()
  for c in [' ','\\','/','-','.']: key = key.replace(c,'')
  for c in r2l_translit: key = key.replace( c, r2l_translit[c] )
  if key in keys_equi: key = keys_equi[key]
  return key


def year2color( year_str ):
  if year_str=="": return ""
  #min_y = 1960.; min_c = 20.
  #max_y = 2016.; max_c = 255.
  y = float(year_str)
  #y_scale = 1 - (max_y-y)/(max_y-min_y)
  #i = int( min_c + y_scale * (max_c - min_c) )
  #col = "#%02x%02x%02x" % (i,i,i) # FFFFFF
  if y < 1980: col = "#000000"
  elif y < 1998: col = "#555555"
  elif y < 2008: col = "#aaaaaa"
  else: col = "#ffffff"
  return col

def nbcit2size( nb_cit ):
  sz = 10 + 10*nb_cit
  if sz > 150: sz = 150;
  return sz

def localize( s ):
  book_txt = str(s)
  book_lang = ""
  lat_c = len(['1' for c in book_txt if 'A' <= c <= 'z']); # количество латинских символов
  rus_c = len(['1' for c in book_txt if 'А' <= c <= 'я']); # количество русских символов
  if lat_c > rus_c:
    book_lang = 'L'
    for i in r2l: book_txt = book_txt.replace( i, r2l[i] )
  else:
    book_lang = 'R'
    for i in l2r: book_txt = book_txt.replace( i, l2r[i] )
    for i in l2r_oneway: book_txt = book_txt.replace( i, l2r_oneway[i] )
  return book_txt,book_lang




def word_wrap( book_txt ):
  wrapped = ""
  counter = 0
  for b in book_txt.split(' '):
    if counter + len(b) > 20: wrapped = wrapped + '\n' + b; counter = len(b)
    else: wrapped = wrapped + ' ' +  b; counter = counter + len(b) + 1
  return wrapped








G = nx.DiGraph()
root = et.Element("root")
books_by_authors = {}
diss_authors = []
phd_list = []
equi = {}
keys_equi = {}

# diss_list = []
for node in et.parse("0.xml").findall('.//disser'):
  current_dis = {}
  for tag in [ 'author', 'author_short', 'title', 'inst', 'instshort', 'fieldid', 'fieldname', 'level', 'directorstatus', 'director', 'city', 'year', 'fileid', 'filename', 'udk', 'bib_src', 'pages' ]:
    if tag in node.attrib: current_dis[tag] = node.attrib[tag]
    else: current_dis[tag] = ""
  current_dis['author_short'] = short_name( current_dis['author'] )
  diss_authors.append( current_dis['author_short'] )
  current_dis['dir_short'] = short_name( current_dis['director'] )
  phd_list.append( current_dis )

  disser_node = et.SubElement( root,"disser" )
  for tag in [ 'author', 'author_short', 'title', 'inst', 'instshort', 'fieldid', 'fieldname', 'level', 'directorstatus', 'director', 'city', 'year', 'fileid', 'filename', 'udk', 'bib_src', 'pages' ]: disser_node.set( tag,current_dis[tag] )

  books_list = []
  if current_dis['filename'] not in ["", "-----"]:
    if current_dis['bib_src'] == 'txt':
      with open( current_dis['filename'], 'r') as f:
        books_list = [ book.strip('\n\r').decode('utf-8') for book in f.readlines() if len(book) > 10 ]
    else:
      bibliography_node = html.parse( current_dis['filename'], et.XMLParser( recover=True ) )     #bk = []
      books_list_tmp = bibliography_node.findall( ".//{%s}div[@class='field field-type-filetext field-field-biblio']/{%s}div[@class='field-items']/{%s}div[@class='field-item odd']/{%s}p" % (XHTML_NS,XHTML_NS,XHTML_NS,XHTML_NS) )
      for element in books_list_tmp:
        books_list.append( ''.join(element.itertext()) ) # Теперь список содержит только библиографическую строку

    # Ключ из имени автора диссертации
    c_sh = name2key( current_dis['author_short'] )
    # diss_authors[ c_sh ] = current_dis['author_short']

    # Ключ из ФИО руководителя
    dir_short = short_name( current_dis['director'] )
    d_sh = name2key( dir_short )

    G.add_node( c_sh )
    G.node[c_sh]['label'] = current_dis['author_short'] + '\n' + current_dis['year']
    G.node[c_sh]['type'] = 'diss'
    G.node[c_sh]['inst'] = current_dis['instshort']
    G.node[c_sh]['year'] = current_dis['year']
    G.node[c_sh]['color'] = year2color( current_dis['year'] ) # ("%2x" % (int(current_dis['year']) - 1900))*3

    # Разбор библиографической записи
    # Самое длинное поле -- название?
    for book_string in books_list:
      book_lang = ''
      book_txt = book_string[ book_string.find('.')+1: ] # Отбросить число в начале ссылки
      while book_txt[0]==' ': book_txt = book_txt[ 1: ] # Отбросить пробелы в начале

      # Определение языка ссылки, модификации свойственные языку
      book_txt,book_lang = localize( book_txt )
      fields = mark_book_fields( book_txt )
      book_year = get_book_year( fields )

      # Отделение патентов в отдельный элемент
      if 'Пат.' in book_txt or 'Пaт. CШA' in book_txt or 'Патент' in book_txt or 'Patent' in book_txt or 'А.с.' in book_txt or 'заявк' in book_txt.lower():
        patent_node = et.SubElement( disser_node,"patent" )
        patent_node.set( 'source', book_txt )
        continue; # Патенты -- это другая история

      if 'диссер' in book_txt.lower() and 'список' not in book_txt.lower() and 'внедрен' not in book_txt.lower():
        new_disser_node = et.SubElement( disser_node,"linkdiss" ) # <diss_link>
        new_disser_node.set( 'source', book_txt )
        G.add_edge( c_sh, book_txt )
        G.node[book_txt]['type'] = 'linkdiss'
        G.node[book_txt]['label'] = word_wrap( book_txt )
        G.node[book_txt]['year'] = book_year
        G.node[book_txt]['inst'] = ''
        G.node[book_txt]['color'] = year2color( book_year )
        continue

      #G.add_node( book_txt )
      #G.node[book_txt]['type'] = 'book'
      #G.node[book_txt]['label'] = book_txt
      #G.node[book_txt]['year'] = book_year

      book_node = et.SubElement( disser_node,"book" )
      book_node.set( 'source', book_string )

      et.SubElement( book_node,"split" ).text = '|'.join( fields )
      book_node.set( 'year', book_year )

      authors = book2authors( fields )
      for a in authors:
        et.SubElement( book_node,"author" ).text = a
        a_sh = name2key( a )

        # Проверить, есть ли похожая книга в перечне авторов и добавить
        if (book_year != '' and int(book_year) > 1990) and a_sh != d_sh and a_sh != c_sh: # Исключить цитирование себя или своего руководителя
          if a_sh not in books_by_authors: books_by_authors[a_sh] = []
          found = 0
          for bk in [bk for bk,yr in books_by_authors[a_sh]]: # Проходим каждый первый элемент "книга"
            if Levenshtein.ratio( bk, book_txt ) > 0.8: found = 1;
          if found == 0: books_by_authors[a_sh].append( (book_txt,book_year) )

        keys_equi[a_sh] = a_sh

        # Связать эту диссертацию с автором, а если он уже существует -- не добавлять нового
        target_node = '' # если окажется что нет достаточно похожего узла, этот автор будет новым
        for gn in list(G.nodes()): # поиск наиболее похожего узла (gn -- кандидат на похожесть)
          if gn!=a_sh and Levenshtein.ratio( a_sh[1:-2], gn[1:-2] ) > 0.75 and a_sh[0] == gn[0] and a_sh[-2:]==gn[-2:]:
            # нашли узел который уже подходит на роль автора
            target_node = gn; # первая буква и инициалы совпадают, остальное совпадает ~до 2 букв
            # занесём автора-кандидата a_sh в список похожих фамилий
            if target_node not in equi: equi[target_node] = []
            elif a not in equi[target_node]: equi[target_node].append( a )
            # словарь подстановки ключей <= для этого автора (его ключа) принята следующая подстановка
            keys_equi[a_sh] = target_node
            break; # Считаем что автор совпадает 

        if target_node == '':
          target_node = a_sh;
          authors_counter = authors_counter + 1

        # Добавим автора
        if target_node != c_sh and target_node != d_sh: # Без самоцитирования и цитирования руководителя
          G.add_edge( c_sh, target_node )

          if target_node not in equi: equi[target_node] = [a]
          elif a not in equi[target_node]: equi[target_node].append( a )

          if ( 'type' not in G.node[target_node] ) or ('type' in G.node[target_node] and G.node[target_node]['type']!='diss'):
            G.node[target_node]['type'] = 'author'
            G.node[target_node]['label'] = a
            G.node[target_node]['inst'] = ''

      # связать всех авторов этой публикации
      for pair in itertools.permutations( authors, 2):
        key0 = name2key(pair[0]); key1 = name2key(pair[1]); # каждый узел может быть руководителем или аспирантом
        if key0 != key1 and key0 in G.nodes() and key1 in G.nodes() and \
          'type' in G.node[key0] and 'type' in G.node[key1] and \
          G.node[key0]['type']=='author' and G.node[key1]['type']=='author': #and not G.has_edge( pair[1],pair[0] ):
          G.add_edge( key0, key1, weight=2, color='#0000ff' )
      
      book_node.set( 'lang', book_lang )
      books_counter = books_counter + 1


print("Books: ", books_counter)
print("Authors: ", authors_counter)


# for d in sorted(dl, key=lambda dis:dis['year']): print d['year'], ':', d['author']
with open( "1.xml",'w' ) as f: f.write( et.tostring(root, pretty_print=True, encoding="utf-8") )




# Удалить публикации авторов, на которых ссылается недостаточно диссертаций
for gn in list(G.nodes()):
  if 'type' in G.node[gn] and G.node[gn]['type']=='linkdiss':
    for a in diss_authors:
      if a in G.node[gn]['label']:
        G.remove_node( gn )
        break; # -> "новая" диссертация есть в первичном списке работ
    continue;
  # Изменить размер узла соответственно количеству входящих стрелок
  in_edg = len( [i for i in G.in_edges( gn ) if 'type' in G.node[i[0]] and G.node[i[0]]['type'] != 'diss'] )
  G.node[gn]['width'] = nbcit2size( in_edg )
  G.node[gn]['height'] = int( nbcit2size( in_edg )/1.5 )
  G.node[gn]['shape'] = "Ellipse"
  if 'type' in G.node[gn] and G.node[gn]['type']=='diss': continue;
  elif len( [i for i in G.in_edges( gn ) if 'type' in G.node[i[0]] and G.node[i[0]]['type'] == 'diss'] ) < 2: G.remove_node( gn )

best_books = []

for gn in list(G.nodes()):
  # к часто встречающимся авторам добавить их книги
  #if 'type' in G.node[gn] and (G.node[gn]['type']=='author'): #  or G.node[gn]['type']=='linkdiss'
    if gn in books_by_authors:
      for book_txt,book_year in books_by_authors[ gn ]:
        G.add_edge( gn,book_txt )
        G.node[book_txt]['label'] = word_wrap( book_txt )
        G.node[book_txt]['year'] = book_year
        G.node[book_txt]['color'] = year2color( book_year )
        G.node[book_txt]['type'] = "book"
        G.node[book_txt]['inst'] = ''
        best_books.append( book_txt )

#for e in G.edges():
#  if G.node[e[0]]['type'] == 'diss' and G.node[e[1]]['type'] == 'diss':
#    G.edge[e[0]][e[1]]['color'] = "#ff0000"
#    G.edge[e[0]][e[1]]['weight'] = 4

# аспиранты которые стали авторами
for gn in list(G.nodes()):
  if G.node[gn]['type'] == 'diss':
    for e in G.out_edges(gn):
      if G.node[e[1]]['type'] == 'author':
        if e[0] == e[1]:
          G.edge[e[0]][e[1]]['color'] = "#00cc22"
          G.edge[e[0]][e[1]]['weight'] = 4

# Удалить ссылки на диссертации, если эти диссертации специально разобраны



# Удалив многих авторов, нужно удалить книги из списка
#for gn in G.nodes():
#  if 'type' in G.node[gn] and G.node[gn]['type']=='book' and len(G.in_edges(gn))==0 and len(G.out_edges(gn))==0: G.remove_node( gn )



# Авторы, которых мы сичтаем неразличимыми
#for d in sorted(dl, key=lambda dis:dis['year']): print d['year'], ':', d['author']
for el in sorted(equi): # ,key=lambda e:e[0] # , key=equi.__getitem__
  if len( equi[el] ) > 1:
    print(el, ' = ' , ', '.join( equi[el] ))



# Значок публикации может быть размером с точку
for gn in list(G.nodes()):
  if 'type' in G.node[gn] and G.node[gn]['type']!='author' and G.node[gn]['type']!='diss' : #  or G.node[gn]['type']=='linkdiss'
    if gn in books_by_authors:
      for book_txt,book_year in books_by_authors[ gn ]:
        G.node[gn]['width'] = 1
        G.node[gn]['height'] = 1
        G.node[gn]['type'] = 'Rectangle'




nx.write_graphml( G, "2.graphml" )



with open( "6_books_by_authors.txt",'w' ) as f:
  for a in books_by_authors:
    for book_txt,book_year in books_by_authors[a]:
      f.write( book_txt.replace('\n',' ').replace('\r','').encode('utf-8') + "\n" )

book_years = []
for a in books_by_authors:
  for book_txt,book_year in books_by_authors[a]:
    if( int(book_year) > 2010 ):
      book_years.append( (book_txt,book_year) )
      #f.write( book_txt.encode('utf-8') + "\n")

with open( "7_books_by_authors_2000.txt",'w' ) as f:
  for d in sorted( book_years, key=lambda b:b[1]):
    f.write( d[0].replace('\n',' ').replace('\r','').encode('utf-8') + "\n")
    #print d['year'], ':', d['author']

with open( "8_best_books_by_authors.txt",'w' ) as f:
  for b in best_books:
    f.write( b.replace('\n',' ').replace('\r','').encode('utf-8') + "\n" )

#from networkx.drawing.nx_pydot import write_dot
#import matplotlib.pyplot as plt
#nx.draw(G)
#plt.savefig( '2.svg' )
#nx.draw_graphviz( G )
#write_dot( G,'2.dot' )

with open( "bibtex_disser_authors.bib",'w' ) as f:
  for s in phd_list:
    # 'author', 'author_short', 'title', 'inst', 'instshort', 'fieldid', 'fieldname', 'level', 'directorstatus', 'director', 'city', 'year', 'fileid', 'filename', 'udk', 'bib_src'
    a = s['author_short']
    eng_name = str( a[0:a.find(' ')].lower() )
    for c in r2l_translit: eng_name = eng_name.replace( c, r2l_translit[c] )
    f.write( "@Phdthesis{" + eng_name + s['year'].encode('utf-8')              + ",\n" )
    f.write(( "  Title                    = {" + s['title'] + "},\n" ).encode('utf-8'))
    f.write(( "  Author                   = {" + s['author_short'].replace(' ',', ') + "},\n" ).encode('utf-8'))
    f.write(( "  School                   = {" + s['instshort'] + "},\n" ).encode('utf-8'))
    f.write(( "  Year                     = {" + s['year']      + "},\n" ).encode('utf-8'))
    f.write(( "  Address                  = {" + s['city']      + "},\n" ).encode('utf-8'))
    f.write(( "  Pages                    = {" + s['pages']     + "},\n" ).encode('utf-8'))
    if s['level'][0] == 'к':
      f.write(( "  Prof                     = {" + s['dir_short'].replace(' ',', ') + "},\n" ).encode('utf-8'))
    f.write(( "  Speciality               = {" + s['fieldid']     + "},\n" ).encode('utf-8'))
    f.write(( "  Type                     = {" + "дисс. " + s['level']     + "},\n" ).encode('utf-8'))
    f.write(( "  Owner                    = {sigma},\n" ).encode('utf-8'))
    #f.write( u"  Timestamp                = {2015.10.28}")
    f.write(( "}\n\n" ).encode('utf-8'))




