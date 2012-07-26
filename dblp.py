#!/usr/bin/python
# -*- coding: utf-8 -*-

"""

  dblp.py: DBLP Python Library (DBLPY)
  Copyright (C) 2012 Joan Albert Silvestre Cerda (jsilvestre@dsic.upv.es) 
  
  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.

  +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

  - Overview

  This library provide a high-level framework which uses the DBLP XML Requests
  API. You can search the publications of a given author, filter these
  publications when searching for a concrete paper, or even get the bibtex
  citation.  
  
  Due to the limitations of their API, we have to perform a first query to
  search the author key, then another query for each author found (it may return
  more than one author), and finally two queries for every publication found for
  each author. Therefore, the fact of making all this queries considerably slow
  down the speed of the library. This effect increases with the number of
  publications of the considered authors.

  This library was developed for the Pascal2 "LaVie" project, during my stay on
  Ljubljana (Slovenija).

  ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

  - Changelog
    <> Version 1.0 (25 Jul 2012)
       + First Version.

"""

import urllib2, sys, unicodedata, string
from xml.dom.minidom import parseString
import re

# encode string in utf-8 (to bytestream)
def _u8(string) : return string.encode('utf-8')

# decode string in utf-8 (to Unicode)
def _un(string) : return string.decode('utf-8')

# removes tildes and white-spaces for a given string
def _remove_accents(data): return ''.join(x for x in unicodedata.normalize('NFKD', data) if x in string.ascii_letters)

# computes the levenshtein edit distance between two strings
def _levenshtein(s1, s2): 
  d = {}
  lenstr1 = len(s1)
  lenstr2 = len(s2)
  for i in xrange(-1,lenstr1+1):
    d[(i,-1)] = i+1
  for j in xrange(-1,lenstr2+1):
    d[(-1,j)] = j+1
    
  for i in xrange(lenstr1):
    for j in xrange(lenstr2):
      if s1[i] == s2[j]:
        cost = 0
      else:
        cost = 1
      d[(i,j)] = min(
                     d[(i-1,j)] + 1, # deletion
                     d[(i,j-1)] + 1, # insertion
                     d[(i-1,j-1)] + cost, # substitution
                     )
      if i and j and s1[i]==s2[j-1] and s1[i-1] == s2[j]:
        d[(i,j)] = min (d[(i,j)], d[i-2,j-2] + cost) # transposition
 
  return d[lenstr1-1,lenstr2-1]

class SearchError(Exception):
    """
    Base class for DBLP Search exceptions.
    """
    pass

class Publication():
  """
  Represents a Publication, built from the data given by the xml request on DBLP.
  """
  
  def __init__(self, pkey, ptype, title, authors, url=None, journal=None, booktitle=None, editor=None, volume=None, pages=None, number=None, series=None, chapter=None, publisher=None, adress=None, year=None, month=None, isbn=None):
    self.pkey = pkey
    self.ptype = ptype
    self.title = title
    self.authors = authors
    self.url = url
    self.journal = journal
    self.booktitle = booktitle
    self.editor = editor
    self.volume = volume
    self.pages = pages
    self.number = number
    self.series = series
    self.chapter = chapter
    self.publisher = publisher
    self.adress = adress
    self.year = year
    self.month = month
    self.isbn = isbn
    self.bibtex = None

  # This object string representation should be improved.
  
  def __repr__(self):
    
    authors_string=""
    if len(self.authors) > 0:
      for i in range(len(self.authors)-1):
        authors_string+=self.authors[i]+", "
      authors_string+=self.authors[len(self.authors)-1]+'.'
    
    citation = self.title
    if authors_string != "":
      citation +=' '+authors_string

    if self.journal != None:
      citation +=' '+self.journal+'.'
    elif self.booktitle != None:
      citation +=' '+self.booktitle+'.'
    
    return citation

  # Prints the bibtex citation, if avariable
  
  def export_bibtex(self):
  
    if self.bibtex == None:
      text = None
    else:
      text = "" 
      for b in self.bibtex:
        text += b

    return text

class DBLPResult(): 
  """
  Result of the query on DBLP. It comprises a list of Publications, the author name/keys found, and the query text.
  """
  
  def __init__(self, query, publications, authors):

    self.query = query
    self.publications = publications
    self.authors = authors

  def get_publications(self):

    return self.publications
  
  def get_authors(self):

    return self.authors
  
  # Search for a concrete publication by title.
  # It performs a comparison case-insensitive, without spaces, tildes, and non-aplhanumeric chars.
  # It can also perform a levenshtein edit distance for cases in which the exact title is not known.
  # The CER (character error rate) is computed, and if the best CER is below a given threshold, then we return its publication.
  
  def search_by_title(self, title, lev=False, threshold=0.2):

    t2 = _remove_accents(_un(title.lower()))

    if not(lev):
      for p in self.publications:
        t1 = _remove_accents(_un(p.title.lower()))
        if t1 == t2: return p

    else:
      min_cer = 100.0
      best = None
      for i in range(len(self.publications)):
        t1 = _remove_accents(_un(self.publications[i].title.lower()))
        cer = float(_levenshtein(t1,t2))/float(len(t1)) # CER (character error rate)
        
        if cer < 0.01: return self.publications[i]
        if cer < min_cer:
          min_cer = cer
          best = self.publications[i]
      
      if min_cer < threshold: # if CER is below a given threshold, then we return this publication.
        return best

    return None

class DBLPSearch:
  """
  Class which performs the queries on DBLP.
  """

  SEARCH_AUTHOR="http://dblp.uni-trier.de/search/author?xauthor=%s"
  GET_AUTHOR_PUBLICATIONS="http://dblp.uni-trier.de/rec/pers/%s/xk"
  GET_BIBTEX_XML="http://dblp.uni-trier.de/rec/bibtex/%s.xml"
  GET_BIBTEX_PLAIN="http://dblp.uni-trier.de/rec/bibtex/%s"

  def __init__(self,query):
    
    # We substitute blank spaces with it's URL representation
    self.query='%20'.join(query.split())

  # This is the only callable method from outside. Performs the search of all publications for a given author name.
  # It must be noted that more than one author can be found, so it retrieves all publications for all authors.
  # A publication title can be given, so the query process ends when the required publication is found, and returns only
  # that publication. If no publication is found, then it returns a None object.

  def search(self, title=None, lev=False, threshold=0.2):

    # Performs the author query, parses the xml response, and gather the author DBLP keys.
    authors_xml = parseString(self._query(DBLPSearch.SEARCH_AUTHOR%(self.query)))
    author_keys = self._get_authors(authors_xml) # is a list of tuples (author_key,author_name)

    publications = []

    # for every author found, we query for his/hers publications, parse the xml response, and for each publication, get its DBLP key.
    for a in author_keys: 
      publications_xml = parseString(self._query(DBLPSearch.GET_AUTHOR_PUBLICATIONS%(a[0])))
      publications_keys = self._get_publications(publications_xml)

      # for all publications, we perform one more query for retrieve the bibtex xml information.
      # With this info, we create a Publication object. We also query for the bibtex citation,
      # and finally we append the Publication object to a list.
      for p in publications_keys:
        publication_xml = parseString(self._query(DBLPSearch.GET_BIBTEX_XML%(p)))
        publication_bibtex = self._get_bibtex(publication_xml, p)
        
        publication_bibtex_plain = self._query(DBLPSearch.GET_BIBTEX_PLAIN%(p))
        publication_bibtex.bibtex = self._clean_bibtex_html(publication_bibtex_plain)
        
        if title != None:
          if not(lev):
            isTarget = self._is_target(publication_bibtex.title, title)
          else:
            isTarget = self._is_target(publication_bibtex.title, title, lev=True, threshold=threshold)

          if isTarget:
            return DBLPResult(' '.join(self.query.split('%20')), [publication_bibtex], author_keys)
        else:
          publications.append(publication_bibtex)
    
    if title != None: 
      return None

    # We return a DBLPResult object with all publications found.
    return DBLPResult(' '.join(self.query.split('%20')), publications, author_keys)

 
  # This method compares two titles and decide if they are the same (or roughly the same).
  # It performs a comparison case-insensitive, without spaces, tildes, and non-aplhanumeric chars.
  # It can also perform a levenshtein edit distance for cases in which the exact title is not known.
  # The CER (character error rate) is computed, and if it is below a given threshold, then we accept.
  
  def _is_target(self, t1, t2, lev=False, threshold=0.2):

    t1 = _remove_accents(_un(t1.lower()))
    t2 = _remove_accents(_un(t2.lower()))

    if not(lev):
      if t1 == t2: return True

    else:
      cer = float(_levenshtein(t1,t2))/float(len(t1)) # CER (character error rate)  
      if cer < threshold: # if CER is below a given threshold, then we accept.
        return True

    return False

  # This method perfoms a query to DBLP and returns (hopefully) the response data.
  
  def _query(self,url):
    
    try:
      file = urllib2.urlopen(url)
    except URLError:
      raise SearchError, "DBLP search xml request failed: %s" %(url)

    data = file.read()
    file.close()
    return data
    
  # This method recieves as input a parsed xml, and outputs a list of author keys
  
  def _get_authors(self,xml):
    
    if len(xml.getElementsByTagName('author')) == 0:    
      raise SearchError, 'No results found for query: "%s"' %(' '.join(self.query.split('%20')))
    
    authors_xml=xml.getElementsByTagName('author')
    authors=[]

    for a in authors_xml:
      author_id=a.getAttribute('urlpt')
      author_name=self._strip_tags(a.toxml())
      authors.append((author_id, author_name))
    
    return authors

  # This method recieves as input a parsed xml, and outputs a list of publication keys
  
  def _get_publications(self,xml):

    publications_xml=xml.getElementsByTagName('dblpkey')
    publications=[]

    for p in publications_xml:
      if p.hasAttribute('type'): continue
      publication_key=self._strip_tags(p.toxml())
      publications.append(publication_key)
    
    return publications
 
  # This method recieves as input a parsed xml, and outputs a Publication object.
  
  def _get_bibtex(self,xml,pkey):

    if len(xml.getElementsByTagName('article')) > 0:
      ptype = "article"
    elif len(xml.getElementsByTagName('inproceedings')) > 0:
      ptype = "inproceedings"
    elif len(xml.getElementsByTagName('proceedings')) > 0:
      ptype = "proceedings"
    elif len(xml.getElementsByTagName('book')) > 0:
      ptype = "book"
    elif len(xml.getElementsByTagName('incollection')) > 0:
      ptype = "incollection"
    elif len(xml.getElementsByTagName('phdthesis')) > 0:
      ptype = "phdthesis"
    elif len(xml.getElementsByTagName('mastersthesis')) > 0:
      ptype = "mastersthesis"
    elif len(xml.getElementsByTagName('www')) > 0:
      ptype = "www"
    else:
      ptype = None

    title=_u8(self._strip_tags(xml.getElementsByTagName('title')[0].toxml()))
    
    authors_xml=xml.getElementsByTagName('author')
    authors=[]
    
    for a in authors_xml:
      authors.append(_u8(self._strip_tags(a.toxml())))

    url_xml=xml.getElementsByTagName('ee')
    if len(url_xml) != 0:
      url=_u8(self._strip_tags(url_xml[0].toxml()))
    else:
      url=None

    journal_xml=xml.getElementsByTagName('journal')
    if len(journal_xml) != 0:
      journal=_u8(self._strip_tags(journal_xml[0].toxml()))
    else:
      journal=None
    
    booktitle_xml=xml.getElementsByTagName('booktitle')
    if len(booktitle_xml) != 0:
      booktitle=_u8(self._strip_tags(booktitle_xml[0].toxml()))
    else:
      booktitle=None

    editor_xml=xml.getElementsByTagName('editor')
    if len(editor_xml) != 0:
      editor=_u8(self._strip_tags(editor_xml[0].toxml()))
    else:
      editor=None

    volume_xml=xml.getElementsByTagName('volume')
    if len(volume_xml) != 0:
      volume=_u8(self._strip_tags(volume_xml[0].toxml()))
    else:
      volume=None

    pages_xml=xml.getElementsByTagName('pages')
    if len(pages_xml) != 0:
      pages=_u8(self._strip_tags(pages_xml[0].toxml()))
    else:
      pages=None

    number_xml=xml.getElementsByTagName('number')
    if len(number_xml) != 0:
      number=_u8(self._strip_tags(number_xml[0].toxml()))
    else:
      number=None

    series_xml=xml.getElementsByTagName('series')
    if len(series_xml) != 0:
      series=_u8(self._strip_tags(series_xml[0].toxml()))
    else:
      series=None

    chapter_xml=xml.getElementsByTagName('chapter')
    if len(chapter_xml) != 0:
      chapter=_u8(self._strip_tags(chapter_xml[0].toxml()))
    else:
      chapter=None

    publisher_xml=xml.getElementsByTagName('publisher')
    if len(publisher_xml) != 0:
      publisher=_u8(self._strip_tags(publisher_xml[0].toxml()))
    else:
      publisher=None

    adress_xml=xml.getElementsByTagName('adress')
    if len(adress_xml) != 0:
      adress=_u8(self._strip_tags(adress_xml[0].toxml()))
    else:
      adress=None

    year_xml=xml.getElementsByTagName('year')
    if len(year_xml) != 0:
      year=_u8(self._strip_tags(year_xml[0].toxml()))
    else:
      year=None

    month_xml=xml.getElementsByTagName('month')
    if len(month_xml) != 0:
      month=_u8(self._strip_tags(month_xml[0].toxml()))
    else:
      month=None

    isbn_xml=xml.getElementsByTagName('isbn')
    if len(isbn_xml) != 0:
      isbn=_u8(self._strip_tags(isbn_xml[0].toxml()))
    else:
      isbn=None

    return Publication(pkey,ptype,title,authors,url,journal,booktitle,editor,volume,pages,number,series,chapter,publisher,adress,year,month,isbn)

  # This method recieves plain html code and strips all html tags.
  
  def _strip_tags(self, html):
    p = re.compile(r'<.*?>')
    return p.sub('', html)

  # This method recieves html code from the bibtex citation query, and cleans it up.
  
  def _clean_bibtex_html(self, html):
    res = re.compile('<pre>(.*?)</pre>', re.DOTALL |  re.IGNORECASE).findall(html)
    bibtex = []
    for r in res: bibtex.append(self._strip_tags(r))
    return bibtex

"""
  Library ends here. From this point begins the main function, to test our library :)
"""

if __name__ == '__main__':

  from optparse import OptionParser

  # Function to print the results
  def print_publication(p,options):
  
    if options.u_flag:
      if p.url != None: 
        print p.url
      else: 
        print "NO_URL"

    elif options.b_flag:
      bibtex = p.export_bibtex()
      if bibtex != None: 
        print bibtex
      else: 
        print "NO_BIBTEX"
  
    else:
      print p

  # Option parser definition
  usage = "%prog [options] <query_string>"
  desc = "dblp.py: DBLP Python Library (DBLPY). You can search the publications of a given author, filter these publications when searching for a concrete paper, or even get the bibtex citation."
  parser = OptionParser(usage=usage, description=desc)

  parser.add_option("-u", "--only_url", dest="u_flag", action="store_true", default=False, help="Shows only urls for each publication, if avariable.")
  parser.add_option("-b", "--only_bibtex", dest="b_flag", action="store_true", default=False, help="Shows only bibtex for each publication.")
  parser.add_option("-t", "--title", dest="title", help="Search for a concrete publication title. Double-quoted title IS REQUIRED, otherwise it will take oly the first word.")
  parser.add_option("-a", "--approx_search", dest="a_flag", action="store_true", default=False, help="When enabled the --title option, it performs an approximate search by means of levenshtein edit distance (actually CER, character error rate).")
  parser.add_option("-l", "--threshold", dest="threshold", help="CER Acceptance threshold [0.0-1.0] for the approximate title search (default = 0.2).")
  parser.add_option("-q", "--query_title_search", dest="q_flag", action="store_true", default=False, help="When enabled the --title option, the title search is performed during the dblp query instead of wait until the query ends, so the search become faster but possibly inaccuratte if the --approx_search option is enabled (it will return the first publication with CER < threshold).")

  (options, args) = parser.parse_args()

  if len(args) < 1:
    parser.error("At least one argument is needed to perform a query.")
    sys.exit(100)

  query=' '.join(args[0:])

  # Create the DBLPSearch object
  dblp = DBLPSearch(query)
  
  # Let's Rock!

  if options.title != None: # Publication title search enabled

    if options.q_flag: # title search during dblp query enabled

      if options.a_flag: # approximate search enabled

        if options.threshold != None: # a threshold for approximate search is provided
          
          if float(options.threshold) >= 0.0 and float(options.threshold) <= 1.0:
            search_result = dblp.search(options.title, lev=True, threshold=options.threshold)
          else:
            parser.error("CER Threshold must be a float between [0.0-1.0].")
            sys.exit(101)
        
        else: # use default threshold
          search_result = dblp.search(options.title, lev=True)
      
      else: # approximate search disabled => "exact" query
        search_result = dblp.search(options.title)
      
      # Evaluate and output result
      if search_result != None:
        p = search_result.get_publications()[0]
        print_publication(p, options)
      else:
        print 'Title "'+options.title+'" not found in '+query+'\'s publications.'

    
    else: # title search during dblp query disabled => the search is performed after the queries end.

      search_result = dblp.search() # perform the dblp queries and gather all publications.

      if options.a_flag: # approximate search enabled

        if options.threshold != None: # a threshold for approximate search is provided

          if float(options.threshold) >= 0.0 and float(options.threshold) <= 1.0:
            p = search_result.search_by_title(options.title, lev=True, threshold=float(options.threshold))
          else:
            parser.error("CER Threshold must be a float between [0.0-1.0].")
            sys.exit(101)

        else: # use default threshold
          p = search_result.search_by_title(options.title, lev=True)

      else: # approximate search disabled => "exact" query
        p = search_result.search_by_title(options.title)

      # Evaluate and output result
      if p != None:
        print_publication(p, options)
      else:
        print 'Title "'+options.title+'" not found in '+query+'\'s publications.'

  else: # Publication title search disabled => Output all publications
    
    # perform the dblp queries and gather all publications.
    search_result = dblp.search()
    publications = search_result.get_publications()

    # Output results
    for p in publications:
      print_publication(p, options)

